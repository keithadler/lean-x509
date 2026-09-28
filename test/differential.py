#!/usr/bin/env python3
"""Differential test: the compiled Lean decoder against OpenSSL, over every root in a trust store.

For each certificate the decoder accepts, the serial, validity dates, CA flag, path length, DNS names,
RSA key size and exponent, and (for self-signed RSA/SHA-256 roots) the self-signature must agree with
OpenSSL. Certificates the decoder refuses are listed with what makes them out of scope, so a refusal is
never silent. This is a test, not a proof: it checks the compiled code on real inputs.

    python3 test/differential.py [bundle.pem]      (default: /etc/ssl/cert.pem)
"""
import json, os, re, subprocess, sys, tempfile, datetime

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXE = os.path.join(ROOT, ".lake", "build", "bin", "x509")
bundle = sys.argv[1] if len(sys.argv) > 1 else "/etc/ssl/cert.pem"

pems = re.findall(r"-----BEGIN CERTIFICATE-----.+?-----END CERTIFICATE-----", open(bundle).read(), re.S)
tmp = tempfile.mkdtemp()
files = []
for i, pem in enumerate(pems):
    p = os.path.join(tmp, f"{i:03}.der")
    der = subprocess.run(["openssl", "x509", "-outform", "der"], input=pem.encode(), capture_output=True,
                         check=True).stdout
    open(p, "wb").write(der)
    files.append(p)

ours = {}
for line in subprocess.run([EXE, "show", *files], capture_output=True, text=True, check=True).stdout.splitlines():
    j = json.loads(line)
    ours[j["file"]] = j


def openssl(path, *args):
    return subprocess.run(["openssl", "x509", "-inform", "der", "-in", path, "-noout", *args],
                          capture_output=True, text=True).stdout


def stamp(s):
    d = datetime.datetime.strptime(s.strip().replace("  ", " "), "%b %d %H:%M:%S %Y GMT")
    return int(d.strftime("%Y%m%d%H%M%S"))


def why_refused(text):
    """What about this certificate is outside what the decoder accepts."""
    reasons = []
    if "Version: 1" in text:
        reasons.append("v1 certificate")
    if "Public Key Algorithm: rsaEncryption" in text and not re.search(r"Exponent:", text):
        reasons.append("RSA key unreadable")
    return ", ".join(reasons) or "see the certificate"


agree, refused, disagree = 0, [], []
self_checked, self_ok = 0, 0
for f in files:
    j = ours[f]
    text = openssl(f, "-text")
    subject = openssl(f, "-subject", "-nameopt", "RFC2253").strip()
    if "reject" in j:
        refused.append((subject, why_refused(text)))
        continue
    problems = []
    serial = openssl(f, "-serial").strip().split("=")[1].lower()
    # The Lean side prints the serial's DER contents; OpenSSL prints its magnitude (with a "-" when negative).
    lean = int(j["serial"], 16) if j["serial"] else 0
    if j["serial"] and int(j["serial"][:2], 16) >= 0x80:
        lean = lean - (1 << (4 * len(j["serial"])))
    theirs = -int(serial[1:], 16) if serial.startswith("-") else int(serial, 16)
    if lean != theirs:
        problems.append(f"serial {serial} vs {j['serial']}")
    nb = stamp(openssl(f, "-startdate").split("=")[1])
    na = stamp(openssl(f, "-enddate").split("=")[1])
    if (nb, na) != (j["notBefore"], j["notAfter"]):
        problems.append(f"dates {nb}-{na} vs {j['notBefore']}-{j['notAfter']}")
    bc = re.search(r"X509v3 Basic Constraints:.*?\n\s*(.*?)\n", text)
    ca = bool(bc and "CA:TRUE" in bc.group(1))
    pl = re.search(r"pathlen:(\d+)", bc.group(1)) if bc else None
    if ca != j["isCA"] or (int(pl.group(1)) if pl else None) != j["pathLen"]:
        problems.append(f"basicConstraints {bc.group(1) if bc else None} vs {j['isCA']} {j['pathLen']}")
    san = re.search(r"X509v3 Subject Alternative Name:.*?\n\s*(.*?)\n", text)
    dns = [x.strip()[4:] for x in san.group(1).split(",") if x.strip().startswith("DNS:")] if san else []
    if dns != j["dns"]:
        problems.append(f"dns {dns} vs {j['dns']}")
    bits = re.search(r"Public-Key: \((\d+) bit\)", text)
    if "rsaBits" in j["key"]:
        exp = re.search(r"Exponent: (\d+)", text)
        if int(bits.group(1)) != j["key"]["rsaBits"] or int(exp.group(1)) != j["key"]["e"]:
            problems.append(f"key {bits.group(1)}/{exp.group(1)} vs {j['key']}")
    if j["selfSignatureVerifies"] is not None and "sha256WithRSAEncryption" in text.split("Signature Value")[0]:
        self_checked += 1
        theirs = subprocess.run(["openssl", "verify", "-CAfile", f, "-check_ss_sig", f],
                                capture_output=True, text=True)
        # openssl verify needs PEM; fall back to a PEM copy
        pem = f[:-4] + ".pem"
        subprocess.run(["openssl", "x509", "-inform", "der", "-in", f, "-out", pem], check=True)
        theirs = subprocess.run(["openssl", "verify", "-no_check_time", "-CAfile", pem, "-check_ss_sig", pem],
                                capture_output=True, text=True).stdout.strip().endswith("OK")
        if theirs != j["selfSignatureVerifies"]:
            problems.append(f"self-signature openssl={theirs} lean={j['selfSignatureVerifies']}")
        elif theirs:
            self_ok += 1
    if problems:
        disagree.append((subject, problems))
    else:
        agree += 1

print(f"{len(files)} certificates in {bundle}")
print(f"  {agree} decoded, every field agreeing with OpenSSL")
print(f"  {self_checked} self-signed RSA/SHA-256 roots: {self_ok} self-signatures verified by both")
print(f"  {len(refused)} refused by the strict decoder:")
counts = {}
for _, r in refused:
    counts[r] = counts.get(r, 0) + 1
for r, n in sorted(counts.items(), key=lambda x: -x[1]):
    print(f"    {n:3}  {r}")
if disagree:
    print(f"  {len(disagree)} DISAGREEMENTS:")
    for s, p in disagree:
        print("   ", s, p)
    sys.exit(1)
print("OK: no disagreements")
