#!/usr/bin/env python3
"""Builds the cross-library corpus: a test PKI and certificates that are wrong in one way each.

Every certificate a library should refuse is *re-signed* after it is changed, so the signature is
always valid: a library that accepts one of these accepted the flaw itself, not a broken signature.
(The approach of Frankencerts, Brubaker et al., IEEE S&P 2014.)

    python3 test/crosscheck/corpus.py OUTDIR

writes OUTDIR/*.der and OUTDIR/manifest.json. Each manifest entry names the leaf, the intermediates in
order, the trust anchor, the host name, what RFC 5280 or X.690 requires, and why.
"""
import datetime as dt
import json
import os
import sys

from cryptography import x509
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import padding, rsa
from cryptography.x509.oid import ExtendedKeyUsageOID, NameOID

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import der  # noqa: E402

NOW = dt.datetime(2026, 9, 27, 12, 0, tzinfo=dt.timezone.utc)
HOST = "test.example"


def key():
    return rsa.generate_private_key(public_exponent=65537, key_size=2048)


def name(cn):
    return x509.Name([x509.NameAttribute(NameOID.COUNTRY_NAME, "US"),
                      x509.NameAttribute(NameOID.ORGANIZATION_NAME, "lean-x509 test PKI"),
                      x509.NameAttribute(NameOID.COMMON_NAME, cn)])


def d(y, m, dd):
    return dt.datetime(y, m, dd, tzinfo=dt.timezone.utc)


def cert(subject, subject_key, issuer, issuer_key, *, ca, path_len=None, ku=None, eku=None, san=None,
         not_before=d(2025, 1, 1), not_after=d(2030, 1, 1), serial=None, extra=()):
    b = (x509.CertificateBuilder().subject_name(name(subject)).issuer_name(name(issuer))
         .public_key(subject_key.public_key()).serial_number(serial or x509.random_serial_number())
         .not_valid_before(not_before).not_valid_after(not_after)
         .add_extension(x509.BasicConstraints(ca=ca, path_length=path_len), critical=True))
    if ku is not None:
        b = b.add_extension(ku, critical=True)
    if eku is not None:
        b = b.add_extension(x509.ExtendedKeyUsage(eku), critical=False)
    if san is not None:
        b = b.add_extension(x509.SubjectAlternativeName([x509.DNSName(n) for n in san]), critical=False)
    b = b.add_extension(x509.SubjectKeyIdentifier.from_public_key(subject_key.public_key()), critical=False)
    b = b.add_extension(x509.AuthorityKeyIdentifier.from_issuer_public_key(issuer_key.public_key()),
                        critical=False)
    for ext, crit in extra:
        b = b.add_extension(ext, critical=crit)
    return b.sign(issuer_key, hashes.SHA256()).public_bytes(serialization.Encoding.DER)


CA_KU = x509.KeyUsage(digital_signature=False, content_commitment=False, key_encipherment=False,
                      data_encipherment=False, key_agreement=False, key_cert_sign=True, crl_sign=True,
                      encipher_only=False, decipher_only=False)
LEAF_KU = x509.KeyUsage(digital_signature=True, content_commitment=False, key_encipherment=True,
                        data_encipherment=False, key_agreement=False, key_cert_sign=False, crl_sign=False,
                        encipher_only=False, decipher_only=False)
SERVER = [ExtendedKeyUsageOID.SERVER_AUTH]


def resign(der_bytes, issuer_key, change):
    """Applies `change` to the certificate's tree (it may touch the TBS), then signs the TBS again."""
    t = der.tree(der_bytes)
    change(t)
    tbs = der.encode(der.at(t, 0))
    sig = issuer_key.sign(tbs, padding.PKCS1v15(), hashes.SHA256())
    t[1][2] = [0x03, b"\x00" + sig]
    return der.encode(t)


def outer(der_bytes, change):
    """Changes only the outer wrapper, which the signature does not cover."""
    t = der.tree(der_bytes)
    r = change(t)
    return r if isinstance(r, bytes) else der.encode(t)


def exts(t):
    return der.at(t, 0, 7, 0)[1]


def ext(t, dotted):
    body = der.oid(dotted)[1]
    return [e for e in exts(t) if e[1][0][1] == body][0]


def build(out):
    os.makedirs(out, exist_ok=True)
    rk, ik, lk, ek, sk = key(), key(), key(), key(), key()
    root = cert("lean-x509 Test Root", rk, "lean-x509 Test Root", rk, ca=True, ku=CA_KU,
                not_after=d(2035, 1, 1))
    inter = cert("lean-x509 Test Intermediate", ik, "lean-x509 Test Root", rk, ca=True, ku=CA_KU)
    san = [HOST, "www." + HOST, "*.wild.example"]

    def leaf(**kw):
        args = dict(ca=False, ku=LEAF_KU, eku=SERVER, san=san, not_before=d(2026, 1, 1),
                    not_after=d(2026, 12, 31))
        args.update(kw)
        return cert(HOST, lk, "lean-x509 Test Intermediate", ik, **args)

    good = leaf()
    files = {"root": root, "inter": inter}
    cases = []

    def add(cid, group, leaf_der, rule, *, host=HOST, chain=("inter",), expect="reject", extra_files=()):
        files[cid] = leaf_der
        for n, b in extra_files:
            files[n] = b
        cases.append({"id": cid, "group": group, "leaf": cid + ".der",
                      "chain": [c + ".der" for c in chain], "anchor": "root.der", "host": host,
                      "expect": expect, "rule": rule})

    # Positive controls: every library should accept these.
    add("valid", "control", good, "a well-formed chain", expect="accept")
    add("valid-www", "control", good, "the certificate names www.test.example", host="www." + HOST,
        expect="accept")
    add("valid-wildcard", "control", good, "*.wild.example covers a.wild.example",
        host="a.wild.example", expect="accept")

    # DER: X.509 certificates must be DER (RFC 5280 §4.1), and DER gives each value one encoding.
    def long_len(t):
        der.at(t, 0, 0, 0).append(lambda n: bytes([0x81, n]))
    add("der-long-length", "DER", resign(good, ik, long_len),
        "X.690 §10.1: the shortest length form (0x81 01 where 01 fits)")

    def zero_pad(t):
        der.at(t, 0, 3).append(lambda n: bytes([0x82, 0x00, n]))
    add("der-length-leading-zero", "DER", resign(good, ik, zero_pad),
        "X.690 §10.1: no leading zero in a long-form length")

    def indefinite(t):
        der.at(t, 0, 4).append(lambda n: b"\x80")
        der.at(t, 0, 4)[1].append([0x00, b""])
    add("der-indefinite-length", "DER", resign(good, ik, indefinite),
        "X.690 §10.1: DER never uses the indefinite length")

    def serial_pad(t):
        s = der.at(t, 0, 1)
        s[1] = b"\x00" + s[1] if s[1][0] < 0x80 else b"\x00\x00" + s[1][1:]
    add("der-integer-padding", "DER", resign(good, ik, serial_pad),
        "X.690 §8.3.2: an INTEGER in the fewest octets")

    def bool_one(t):
        ext(t, "2.5.29.19")[1][1][1] = b"\x01"
    add("der-boolean-01", "DER", resign(good, ik, bool_one), "X.690 §11.1: DER TRUE is 0xFF")

    def crit_false(t):
        e = ext(t, "2.5.29.17")
        e[1].insert(1, [0x01, b"\x00"])
    add("der-default-false-written", "DER", resign(good, ik, crit_false),
        "X.690 §11.5: a DEFAULT value (critical FALSE) is omitted")

    def high_tag(t):
        der.at(t, 0, 1)[0] = 0x1F
        der.at(t, 0, 1).append(lambda n: bytes([0x02, n]))
    add("der-high-tag-for-low", "DER", resign(good, ik, high_tag),
        "X.690 §8.1.2: tag numbers below 31 use one identifier octet")

    def oid_pad(t):
        o = der.at(t, 0, 5, 0, 0, 0)
        o[1] = b"\x80" + o[1]
    add("der-oid-padding", "DER", resign(good, ik, oid_pad),
        "X.690 §8.19.2: no 0x80 padding in an OID subidentifier")

    def time_general(t):
        v = der.at(t, 0, 4)
        v[1][0] = [0x18, b"20" + v[1][0][1]]
    add("rfc-generalizedtime-2026", "DER", resign(good, ik, time_general),
        "RFC 5280 §4.1.2.5: dates through 2049 are UTCTime")

    def feb30(t):
        der.at(t, 0, 4)[1][0][1] = b"260230000000Z"
    add("rfc-february-30", "DER", resign(good, ik, feb30), "RFC 5280 §4.1.2.5: a real calendar date")

    def trailing_in_ext(t):
        e = ext(t, "2.5.29.19")
        e[1][-1][1] = e[1][-1][1] + b"\x00"
    add("der-trailing-in-extension", "DER", resign(good, ik, trailing_in_ext),
        "X.690: an extension's value is exactly one DER value")

    add("der-trailing-byte", "DER", outer(good, lambda t: der.encode(t) + b"\x00"),
        "the certificate is exactly one DER value, nothing after it")

    def outer_zero(t):
        t.append(lambda n: bytes([0x83, 0x00]) + n.to_bytes(2, "big"))
    add("der-outer-length-leading-zero", "DER", outer(good, outer_zero),
        "X.690 §10.1, on the unsigned outer SEQUENCE: same certificate, different bytes")

    def outer_indef(t):
        return b"\x30\x80" + b"".join(der.encode(c) for c in t[1]) + b"\x00\x00"
    add("der-outer-indefinite", "DER", outer(good, outer_indef),
        "X.690 §10.1, on the unsigned outer SEQUENCE: same certificate, different bytes")

    def outer_alg(t):
        der.at(t, 1)[1] = der.at(t, 1)[1][:1]  # outer AlgorithmIdentifier without its NULL
    add("rfc-outer-algorithm-differs", "DER", outer(good, outer_alg),
        "RFC 5280 §4.1.1.2: signatureAlgorithm must equal the TBS signature field")

    # RFC 5280 path validation.
    add("path-unknown-critical-extension", "RFC 5280", leaf(extra=[(x509.UnrecognizedExtension(
        x509.ObjectIdentifier("1.3.6.1.4.1.55555.1"), b"\x05\x00"), True)]),
        "§4.2: refuse a certificate with a critical extension it does not recognize")

    def dup_ext(t):
        exts(t).append([0x30, [c for c in ext(t, "2.5.29.17")[1]]])
    add("path-duplicate-extension", "RFC 5280", resign(good, ik, dup_ext),
        "§4.2: a certificate must not include an extension twice")

    evil = cert("evil.example", ek, HOST, lk, ca=False, ku=LEAF_KU, eku=SERVER, san=["evil.example"],
                not_before=d(2026, 1, 1), not_after=d(2026, 12, 31))
    add("path-leaf-as-ca", "RFC 5280", evil, "§6.1.4 (k): only a CA (cA = TRUE) may issue",
        host="evil.example", chain=("valid", "inter"))

    capl = cert("lean-x509 Test CA pathLen 0", sk, "lean-x509 Test Root", rk, ca=True, path_len=0,
                ku=CA_KU)
    sub_key = key()
    sub = cert("lean-x509 Test Sub CA", sub_key, "lean-x509 Test CA pathLen 0", sk, ca=True, ku=CA_KU)
    deep = cert(HOST, lk, "lean-x509 Test Sub CA", sub_key, ca=False, ku=LEAF_KU, eku=SERVER, san=san,
                not_before=d(2026, 1, 1), not_after=d(2026, 12, 31))
    add("path-length-exceeded", "RFC 5280", deep, "§6.1.4 (m): pathLenConstraint 0 allows no sub-CA",
        chain=("sub", "capl"), extra_files=[("sub", sub), ("capl", capl)])

    nosign_key = key()
    nosign = cert("lean-x509 Test CA no certSign", nosign_key, "lean-x509 Test Root", rk, ca=True,
                  ku=LEAF_KU)
    under = cert(HOST, lk, "lean-x509 Test CA no certSign", nosign_key, ca=False, ku=LEAF_KU,
                 eku=SERVER, san=san, not_before=d(2026, 1, 1), not_after=d(2026, 12, 31))
    add("path-issuer-without-keycertsign", "RFC 5280", under,
        "§6.1.4 (n): an issuer's keyUsage must include keyCertSign", chain=("nosign",),
        extra_files=[("nosign", nosign)])

    old_key = key()
    old = cert("lean-x509 Test CA expired", old_key, "lean-x509 Test Root", rk, ca=True, ku=CA_KU,
               not_after=d(2026, 1, 1))
    under_old = cert(HOST, lk, "lean-x509 Test CA expired", old_key, ca=False, ku=LEAF_KU, eku=SERVER,
                     san=san, not_before=d(2026, 1, 1), not_after=d(2026, 12, 31))
    add("path-expired-intermediate", "RFC 5280", under_old, "§6.1.3 (a)(2): every certificate current",
        chain=("old",), extra_files=[("old", old)])

    add("path-leaf-not-yet-valid", "RFC 5280", leaf(not_before=d(2027, 1, 1), not_after=d(2027, 12, 31)),
        "§6.1.3 (a)(2): not before notBefore")
    add("path-client-only-eku", "RFC 5280", leaf(eku=[ExtendedKeyUsageOID.CLIENT_AUTH]),
        "RFC 5280 §4.2.1.12 with RFC 9525: a server certificate's EKU must allow serverAuth")

    # Host names (RFC 6125 / RFC 9525).
    add("host-other-name", "Host", good, "the certificate does not name other.example",
        host="other.example")
    add("host-wildcard-two-labels", "Host", good, "a wildcard covers one label, not a.b.wild.example",
        host="a.b.wild.example")
    add("host-wildcard-bare", "Host", good, "*.wild.example does not cover wild.example itself",
        host="wild.example")
    add("host-nul-in-name", "Host", leaf(san=["test.example\x00.evil.example"]),
        "a dNSName with a NUL byte names nothing (the 2009 null-prefix attack)")
    add("host-wildcard-partial", "Host", leaf(san=["t*.example"]),
        "RFC 9525 §6.3: a partial-label wildcard MUST be ignored (RFC 6125, replaced in 2023, allowed it)",
        host="test.example")
    add("host-wildcard-tld", "Host", leaf(san=["*.example"]),
        "policy: *.example for x.example (RFC 9525 allows it; browsers refuse it by the Public Suffix List)",
        host="x.example", expect="policy")

    for n, b in files.items():
        open(os.path.join(out, n + ".der"), "wb").write(b)
    json.dump({"now": int(NOW.timestamp()), "now_stamp": NOW.strftime("%Y%m%d%H%M%S"), "cases": cases},
              open(os.path.join(out, "manifest.json"), "w"), indent=1)
    return cases


if __name__ == "__main__":
    cases = build(sys.argv[1] if len(sys.argv) > 1 else "corpus")
    print(f"{len(cases)} cases")
