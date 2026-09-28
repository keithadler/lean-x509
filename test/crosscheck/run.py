#!/usr/bin/env python3
"""Cross-library X.509 harness: the same corpus through every implementation on this machine.

    python3 test/crosscheck/run.py [--out DIR]

Builds the corpus (corpus.py), runs each library's driver, and writes a table of who accepts what to
test/crosscheck/RESULTS.md, plus the raw verdicts to test/crosscheck/results.json. Every certificate
except the controls has exactly one flaw and a valid signature, so "accepts" means the library accepted
that flaw.
"""
import base64
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import corpus  # noqa: E402


def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def pem(path):
    """PEM around the exact bytes: no re-encoding, so malformed DER reaches the library as it is."""
    b = base64.encodebytes(open(path, "rb").read()).decode()
    return "-----BEGIN CERTIFICATE-----\n" + b + "-----END CERTIFICATE-----\n"


def per_case(fn):
    def run(d, m):
        out = {}
        for c in m["cases"]:
            try:
                ok, err = fn(d, m, c)
            except Exception as e:  # noqa: BLE001
                ok, err = False, f"driver error: {e}"
            out[c["id"]] = {"ok": ok, "err": err}
        return out
    return run


def write_pems(d, c, tag):
    leaf = os.path.join(d, f"{tag}-{c['id']}-leaf.pem")
    chain = os.path.join(d, f"{tag}-{c['id']}-chain.pem")
    anchor = os.path.join(d, f"{tag}-anchor.pem")
    open(leaf, "w").write(pem(os.path.join(d, c["leaf"])))
    open(chain, "w").write("".join(pem(os.path.join(d, n)) for n in c["chain"]))
    open(anchor, "w").write(pem(os.path.join(d, c["anchor"])))
    return leaf, chain, anchor


def openssl_driver(binary, tag, hostname=True, strict=False):
    @per_case
    def run(d, m, c):
        if not hostname and c["group"] == "Host":
            return None, "this verify command has no host-name option"
        leaf, chain, anchor = write_pems(d, c, tag)
        cmd = [binary, "verify", "-attime", str(m["now"]), "-CAfile", anchor, "-untrusted", chain,
               "-purpose", "sslserver"]
        if hostname:
            cmd += ["-verify_hostname", c["host"]]
        if strict:
            cmd += ["-x509_strict"]
        r = sh(cmd + [leaf])
        text = (r.stdout + r.stderr).strip()
        ok = r.returncode == 0 and text.endswith("OK")
        return ok, None if ok else text.splitlines()[-1][:200] if text else f"exit {r.returncode}"
    return run


@per_case
def gnutls(d, m, c):
    leaf, chain, anchor = write_pems(d, c, "gnutls")
    bundle = os.path.join(d, f"gnutls-{c['id']}-bundle.pem")
    open(bundle, "w").write(open(leaf).read() + open(chain).read())
    import datetime as dt
    at = dt.datetime.fromtimestamp(m["now"], dt.timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
    r = sh(["gnutls-certtool", "--verify", "--load-ca-certificate", anchor, "--infile", bundle,
            "--verify-hostname", c["host"], "--verify-purpose", "1.3.6.1.5.5.7.3.1", "--attime", at])
    text = (r.stdout + r.stderr)
    ok = r.returncode == 0 and "Chain verification output: Verified." in text
    last = [l for l in text.splitlines() if "verification output" in l.lower() or "error" in l.lower()]
    return ok, None if ok else (last[-1].strip()[:200] if last else text.strip()[-200:])


@per_case
def nss(d, m, c):
    import datetime as dt
    stamp = dt.datetime.fromtimestamp(m["now"], dt.timezone.utc).strftime("%y%m%d%H%MZ")
    if c["group"] == "Host":
        return None, "vfychain does not check host names"
    args = ["vfychain", "-pp", "-u", "1", "-b", stamp, os.path.join(d, c["leaf"])]
    for n in c["chain"]:
        args.append(os.path.join(d, n))
    args += ["-t", os.path.join(d, c["anchor"])]
    r = sh(args)
    text = (r.stdout + r.stderr).strip()
    ok = r.returncode == 0 and "Chain is good!" in text
    return ok, None if ok else (text.splitlines()[-1][:200] if text else f"exit {r.returncode}")


@per_case
def lean(d, m, c):
    exe = os.path.join(ROOT, ".lake", "build", "bin", "x509")
    r = sh([exe, "validate", c["host"], m["now_stamp"], os.path.join(d, c["anchor"]),
            os.path.join(d, c["leaf"])] + [os.path.join(d, n) for n in c["chain"]])
    ok = r.stdout.strip() == "true"
    return ok, None if ok else "validate returned false"


def json_driver(cmd):
    def run(d, m):
        r = sh(cmd + [d])
        out = {}
        for line in r.stdout.splitlines():
            j = json.loads(line)
            out[j["id"]] = {"ok": j["ok"], "err": j.get("err")}
        return out
    return run


def version(cmd):
    try:
        return sh(cmd).stdout.strip().splitlines()[0]
    except Exception:  # noqa: BLE001
        return "?"


def main():
    d = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else tempfile.mkdtemp()
    shutil.rmtree(d, ignore_errors=True)
    corpus.build(d)
    m = json.load(open(os.path.join(d, "manifest.json")))
    with open(os.path.join(d, "manifest.tsv"), "w") as f:
        for c in m["cases"]:
            f.write("\t".join([c["id"], c["leaf"], ",".join(c["chain"]), c["anchor"], c["host"]]) + "\n")
    open(os.path.join(d, "now.txt"), "w").write(str(m["now"]))

    sh(["go", "build", "-o", os.path.join(HERE, "crosscheck-go"), "."], cwd=os.path.join(HERE, "go"))
    sh(["cargo", "build", "--release", "-q"], cwd=os.path.join(HERE, "rust"))
    sh(["swiftc", "-O", "-o", os.path.join(HERE, "crosscheck-apple"), os.path.join(HERE, "swift", "main.swift")])
    brew = "/opt/homebrew/opt"
    sh(["cc", "-O1", "-o", os.path.join(HERE, "crosscheck-mbedtls"), os.path.join(HERE, "c", "mbedtls.c"),
        f"-I{brew}/mbedtls/include", f"-L{brew}/mbedtls/lib", "-lmbedx509", "-lmbedtls", "-ltfpsacrypto"])
    sh(["cc", "-O1", "-o", os.path.join(HERE, "crosscheck-wolfssl"), os.path.join(HERE, "c", "wolfssl.c"),
        f"-I{brew}/wolfssl/include", f"-L{brew}/wolfssl/lib", "-lwolfssl"])
    java = f"{brew}/openjdk/bin/java"
    import cryptography

    libs = [
        ("Lean (this project)", lean, "lean-x509"),
        ("OpenSSL", openssl_driver("/opt/homebrew/bin/openssl", "openssl"),
         version(["/opt/homebrew/bin/openssl", "version"])),
        ("OpenSSL -x509_strict", openssl_driver("/opt/homebrew/bin/openssl", "strict", strict=True),
         "the same, with -x509_strict"),
        ("LibreSSL", openssl_driver("/usr/bin/openssl", "libressl", hostname=False),
         version(["/usr/bin/openssl", "version"]) + " (macOS system openssl; no host-name check)"),
        ("GnuTLS", gnutls, version(["gnutls-certtool", "--version"])),
        ("NSS", nss, "NSS " + version(["/opt/homebrew/opt/nss/bin/nss-config", "--version"]) + " (vfychain)"),
        ("Go", json_driver([os.path.join(HERE, "crosscheck-go")]), version(["go", "version"])),
        ("rustls-webpki", json_driver([os.path.join(HERE, "rust", "target", "release", "crosscheck-webpki")]),
         "rustls-webpki 0.103"),
        ("Python cryptography", json_driver([sys.executable, os.path.join(HERE, "pyca.py")]),
         "cryptography " + cryptography.__version__),
        ("Apple Security", json_driver([os.path.join(HERE, "crosscheck-apple")]),
         "macOS " + version(["sw_vers", "-productVersion"])),
        ("Java", json_driver([java, "--add-exports", "java.base/sun.security.util=ALL-UNNAMED",
                              os.path.join(HERE, "java", "Main.java")]),
         "OpenJDK " + sh([java, "-version"]).stderr.splitlines()[0].split('"')[1] + " (PKIX CertPathValidator)"),
        ("mbedTLS", json_driver([os.path.join(HERE, "crosscheck-mbedtls")]),
         "mbedTLS " + version(["brew", "list", "--versions", "mbedtls"]).split()[-1] + " (current time)"),
        ("wolfSSL", json_driver([os.path.join(HERE, "crosscheck-wolfssl")]),
         "wolfSSL " + version(["brew", "list", "--versions", "wolfssl"]).split()[-1] + " (current time)"),
    ]
    results = {}
    for name, fn, ver in libs:
        print(f"running {name} ({ver})", flush=True)
        results[name] = {"version": ver, "verdicts": fn(d, m)}

    text = json.dumps({"cases": m["cases"], "results": results}, indent=1)
    text = text.replace(d.rstrip("/") + "/", "").replace(os.path.expanduser("~"), "~")
    open(os.path.join(HERE, "results.json"), "w").write(text)
    write_table(m["cases"], results)
    print(open(os.path.join(HERE, "RESULTS.md")).read())


def cell(v, expect):
    if v is None or v.get("ok") is None:
        return "n/a"
    ok = v["ok"]
    if expect == "accept":
        return "accepts" if ok else "**REJECTS**"
    if expect == "policy":
        return "accepts" if ok else "refuses"
    return "**ACCEPTS**" if ok else "refuses"


def write_table(cases, results):
    names = list(results)
    short = {"Lean (this project)": "Lean", "Python cryptography": "pyca", "Apple Security": "Apple",
             "rustls-webpki": "webpki", "OpenSSL -x509_strict": "OpenSSL strict", "wolfSSL": "wolfSSL",
             "mbedTLS": "mbedTLS", "Java": "Java"}
    lines = ["# Cross-library results", "",
             "Generated by `python3 test/crosscheck/run.py`. Every certificate below the controls has one "
             "flaw and a valid signature from the test CA, so **ACCEPTS** means the library accepted "
             "that flaw. Rows marked policy are choices the RFCs leave open, not flaws. n/a: the tool "
             "cannot check that. Validation time 2026-09-27 12:00 UTC.", "",
             "| Library | Version |", "| --- | --- |"]
    for n in names:
        lines.append(f"| {n} | {results[n]['version']} |")
    lines += ["", "| Case | Rule | " + " | ".join(short.get(n, n) for n in names) + " |",
              "| --- | --- | " + " | ".join("---" for _ in names) + " |"]
    group = None
    for c in cases:
        if c["group"] != group:
            group = c["group"]
            lines.append(f"| **{group}** | | " + " | ".join("" for _ in names) + " |")
        cells = [cell(results[n]["verdicts"].get(c["id"]), c["expect"]) for n in names]
        lines.append(f"| `{c['id']}` | {c['rule']} | " + " | ".join(cells) + " |")
    lines += ["", "## Notes", "",
              "- rustls-webpki checks keyCertSign on its main branch (rustls/webpki#452, fixed by #510), "
              "which is not in the current stable release, 0.103.15.",
              "- NSS is exercised through `vfychain`, NSS's own verifier. Firefox validates with "
              "mozilla::pkix on top of NSS, so its answers can differ.",
              "- LibreSSL is the macOS system `openssl` (3.3.6, an old release); its `verify` has no host-name "
              "option, so the host cases are n/a.",
              "- Java runs the PKIX CertPathValidator that JSSE's PKIXValidator uses, plus JSSE's own "
              "HostnameChecker. mbedTLS and wolfSSL check at the current time (the corpus is valid through "
              "2026-12-31); wolfSSL runs through its OpenSSL-compatible X509_STORE with the intermediates "
              "untrusted.",
              "- These are leniencies, not vulnerabilities: every flaw here sits inside bytes the CA signed, "
              "except the three unsigned-wrapper cases, which change a certificate's bytes without changing "
              "what it says.", "",
              "## Accepted flaws, by library", ""]
    for n in names:
        acc = [c["id"] for c in cases if c["expect"] == "reject"
               and (results[n]["verdicts"].get(c["id"]) or {}).get("ok") is True]
        lines.append(f"- **{n}**: {len(acc)}" + (": " + ", ".join(f"`{a}`" for a in acc) if acc else ""))
    open(os.path.join(HERE, "RESULTS.md"), "w").write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
