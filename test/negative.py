#!/usr/bin/env python3
"""Malformed and tampered certificates: every one must be refused.

Each case takes the real *.github.io certificate, changes one thing, and re-encodes it. The Lean decoder
(through the compiled `x509` tool) must refuse the bytes, or, where the bytes are still a well-formed
certificate, chain validation must fail. OpenSSL's answer is shown alongside for comparison: several of
these it accepts.

    python3 test/negative.py [--out DIR]    (--out keeps the generated files)
"""
import os, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXE = os.path.join(ROOT, ".lake", "build", "bin", "x509")
NOW = "20260927120000"
HOST = "keithadler.github.io"


def der_of(pem):
    return subprocess.run(["openssl", "x509", "-in", os.path.join(ROOT, "certs", pem), "-outform", "der"],
                          capture_output=True, check=True).stdout


# ---------- a small DER tree codec with knobs for writing it wrong ----------

def parse(b, i=0):
    t = b[i]; i += 1
    l = b[i]; i += 1
    if l & 0x80:
        n = l & 0x7F
        l = int.from_bytes(b[i:i + n], "big"); i += n
    body = b[i:i + l]
    node = [t, [] if t & 0x20 else body]
    if t & 0x20:
        j = 0
        while j < len(body):
            child, j = parse(body, j)
            node[1].append(child)
    return node, i + l


def enc_len(n):
    if n < 128:
        return bytes([n])
    bs = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([0x80 | len(bs)]) + bs


def encode(node, lenfn=enc_len):
    t, v = node[0], node[1]
    body = b"".join(encode(c, lenfn) for c in v) if t & 0x20 else v
    return bytes([t]) + (node[2](len(body)) if len(node) > 2 else lenfn(len(body))) + body


def tree(der):
    return parse(der)[0]


def at(node, *path):
    for p in path:
        node = node[1][p]
    return node


TBS = (0,)
def tbs_field(n, k):
    return at(n, 0, k)


def ext_list(n):
    return at(n, 0, 7, 0)   # [3] EXPLICIT { SEQUENCE OF Extension }


BASE = der_of("github.io.pem")
YR1, ROOTYR = der_of("yr1.pem"), der_of("root-yr.pem")
ANCHOR = der_of("isrg-root-x1.pem")


def mutate(f):
    n = tree(BASE)
    r = f(n)
    return r if isinstance(r, bytes) else encode(n)


def long_length(n):
    at(n, 0, 0, 0).append(lambda l: bytes([0x81, l]))            # version INTEGER, 0x81 01 instead of 01


def zero_padded_length(n):
    n.append(lambda l: bytes([0x83, 0x00]) + l.to_bytes(2, "big"))  # outer SEQUENCE, length with leading 00


def indefinite(n):
    body = encode(at(n, 0)) + encode(at(n, 1)) + encode(at(n, 2))
    return bytes([0x30, 0x80]) + body + b"\x00\x00"


def trailing(n):
    return encode(n) + b"\x00"


def reserved_ff(n):
    b = encode(n)
    return b[:1] + b"\xff" + b[2:]


def high_tag(n):
    at(n, 0, 1)[0] = 0x1F                                          # serial's tag → multi-byte tag escape
    at(n, 0, 1).append(lambda l: bytes([0x02, l]))


def serial_zero_pad(n):
    s = tbs_field(n, 1)
    s[1] = b"\x00" + s[1]                                          # 00 05 9e … : a redundant leading zero


def v1_explicit(n):
    at(n, 0, 0, 0)[1] = b"\x00"                                    # version written as [0] INTEGER 0


def bool_one(n):
    for e in ext_list(n)[1]:
        if len(e[1]) == 3:
            e[1][1][1] = b"\x01"                                   # critical = 0x01 (BER true, not DER)
            return
    raise RuntimeError("no critical extension")


def critical_false(n):
    e = ext_list(n)[1][0]
    if len(e[1]) == 2:
        e[1].insert(1, [0x01, b"\x00"])                            # critical FALSE written out (DER omits it)
    else:
        e[1][1][1] = b"\x00"


def duplicate_ext(n):
    exts = ext_list(n)[1]
    exts.append([exts[0][0], list(exts[0][1])])


def unknown_critical(n):
    ext_list(n)[1].append([0x30, [[0x06, bytes([0x2b, 0x06, 0x01, 0x04, 0x01, 0x82, 0x37, 0x63, 0x01])],
                                  [0x01, b"\xff"], [0x04, b"\x05\x00"]]])


def generalized_2026(n):
    v = tbs_field(n, 4)
    v[1][0] = [0x18, b"20" + v[1][0][1]]                           # notBefore as GeneralizedTime in 2026


def feb_30(n):
    v = tbs_field(n, 4)
    v[1][0][1] = b"260230000000Z"


def alg_mismatch(n):
    at(n, 0, 2, 0)[1] = bytes.fromhex("2a864886f70d01010c")       # inner algorithm sha384WithRSA


def oid_padded(n):
    at(n, 0, 3, 0, 0, 0)[1] = b"\x80" + at(n, 0, 3, 0, 0, 0)[1]  # issuer's country OID, 55 04 06 → 80 55 04 06


def oid_unterminated(n):
    o = at(n, 0, 3, 0, 0, 0)
    o[1] = o[1][:-1] + bytes([o[1][-1] | 0x80])                  # 55 04 86: the last group never ends


def sig_bit(n):
    s = at(n, 2)
    s[1] = s[1][:-1] + bytes([s[1][-1] ^ 1])                       # flip the last bit of the signature


def tbs_byte(n):
    san = [e for e in ext_list(n)[1] if e[1][0][1] == bytes([0x55, 0x1d, 0x11])][0]
    v = san[1][-1]
    v[1] = v[1].replace(b"github.io", b"github.iP", 1)            # one letter of a DNS name


def leaf_as_ca(n):
    bc = [e for e in ext_list(n)[1] if e[1][0][1] == bytes([0x55, 0x1d, 0x13])][0]
    bc[1][-1][1] = bytes.fromhex("30030101ff")                    # basicConstraints cA = TRUE


CASES = [
    ("long-form length where one byte fits", long_length, "decode"),
    ("length with a leading zero byte", zero_padded_length, "decode"),
    ("indefinite length (BER)", indefinite, "decode"),
    ("a byte after the certificate", trailing, "decode"),
    ("reserved length byte 0xFF", reserved_ff, "decode"),
    ("multi-byte tag escape 0x1F", high_tag, "decode"),
    ("serial with a redundant leading zero", serial_zero_pad, "decode"),
    ("version v1 written out explicitly", v1_explicit, "decode"),
    ("BOOLEAN TRUE as 0x01", bool_one, "decode"),
    ("critical FALSE written out", critical_false, "decode"),
    ("the same extension twice", duplicate_ext, "decode"),
    ("an unknown critical extension", unknown_critical, "decode"),
    ("GeneralizedTime for a 2026 date", generalized_2026, "decode"),
    ("February 30", feb_30, "decode"),
    ("inner and outer signature algorithms differ", alg_mismatch, "decode"),
    ("an OID padded with 0x80", oid_padded, "decode"),
    ("an OID whose last byte says more follows", oid_unterminated, "decode"),
    ("one bit of the signature flipped", sig_bit, "chain"),
    ("one letter of a DNS name changed", tbs_byte, "chain"),
    ("leaf rewritten to claim cA = TRUE", leaf_as_ca, "chain"),
]


def run():
    keep = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else None
    d = keep or tempfile.mkdtemp()
    os.makedirs(d, exist_ok=True)
    for name, b in [("yr1", YR1), ("root-yr", ROOTYR), ("anchor", ANCHOR)]:
        open(os.path.join(d, name + ".der"), "wb").write(b)
    base = os.path.join(d, "base.der")
    open(base, "wb").write(BASE)
    ok = subprocess.run([EXE, "validate", HOST, NOW, os.path.join(d, "anchor.der"), base,
                         os.path.join(d, "yr1.der"), os.path.join(d, "root-yr.der")],
                        capture_output=True, text=True).stdout.strip()
    assert ok == "true", "the unmodified chain must validate"
    print(f"{'case':46} {'Lean':>9}   OpenSSL")
    failures = 0
    for i, (name, f, level) in enumerate(CASES):
        b = mutate(f)
        p = os.path.join(d, f"{i:02}-{f.__name__}.der")
        open(p, "wb").write(b)
        shown = subprocess.run([EXE, "show", p], capture_output=True, text=True).stdout
        decoded = '"reject"' not in shown
        valid = subprocess.run([EXE, "validate", HOST, NOW, os.path.join(d, "anchor.der"), p,
                                os.path.join(d, "yr1.der"), os.path.join(d, "root-yr.der")],
                               capture_output=True, text=True).stdout.strip() == "true"
        lean = "rejected" if not decoded else ("invalid" if not valid else "ACCEPTED")
        o = subprocess.run(["openssl", "x509", "-inform", "der", "-in", p, "-noout"], capture_output=True)
        openssl = "parses" if o.returncode == 0 else "refuses"
        if o.returncode == 0:
            pem = p[:-4] + ".pem"
            subprocess.run(["openssl", "x509", "-inform", "der", "-in", p, "-out", pem], check=True)
            chain = p[:-4] + ".chain.pem"
            with open(chain, "w") as c:
                for x in ("yr1", "root-yr"):
                    c.write(subprocess.run(["openssl", "x509", "-inform", "der", "-in",
                                            os.path.join(d, x + ".der")], capture_output=True,
                                           text=True).stdout)
            anchor = os.path.join(d, "anchor.pem")
            subprocess.run(["openssl", "x509", "-inform", "der", "-in", os.path.join(d, "anchor.der"),
                            "-out", anchor], check=True)
            v = subprocess.run(["openssl", "verify", "-attime", "1790510400", "-CAfile", anchor,
                                "-untrusted", chain, "-verify_hostname", HOST, pem],
                               capture_output=True, text=True).stdout.strip()
            openssl += ", verifies" if v.endswith("OK") else ", fails verify"
        expect_ok = (not decoded) if level == "decode" else (not valid)
        if not expect_ok:
            failures += 1
        print(f"{name:46} {lean:>9}   {openssl}{'' if expect_ok else '   <-- FAIL'}")
    print()
    print("OK: every case refused" if failures == 0 else f"{failures} FAILURES")
    return failures


if __name__ == "__main__":
    sys.exit(1 if run() else 0)
