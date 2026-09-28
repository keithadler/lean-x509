#!/usr/bin/env python3
"""Mutation testing: break the code on purpose, one way at a time, and check something notices.

Each mutant is a single edit that a careless implementation could plausibly contain. For each, the
project is rebuilt; a mutant is killed when a proof or a kernel check stops going through, or, failing
that, when test/negative.py or test/differential.py fails. A mutant that survives is a gap. The source is
restored after every mutant, even on interruption.

    python3 test/mutants.py            (a full run takes a while: every mutant rebuilds the real chain)
"""
import os, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

MUTANTS = [
    ("X509/Der.lean", "long-form length accepted for a length below 128",
     "bs.head? ≠ some 0 ∧ 128 ≤ ofBE bs", "bs.head? ≠ some 0"),
    ("X509/Der.lean", "length bytes with a leading zero accepted",
     "bs.head? ≠ some 0 ∧ 128 ≤ ofBE bs", "128 ≤ ofBE bs"),
    ("X509/Der.lean", "trailing bytes after the certificate ignored",
     "  | some [x] => some x\n", "  | some (x :: _) => some x\n"),
    ("X509/Der.lean", "multi-byte tag escape 0x1F read as an ordinary tag",
     "def tagOk (t : Nat) : Bool := t < 256 && t % 32 != 31", "def tagOk (t : Nat) : Bool := t < 256"),
    ("X509/Prim.lean", "INTEGER with a redundant leading zero accepted",
     "if b < 128 ∧ ¬(b = 0 ∧ c < 128) ∧", "if b < 128 ∧"),
    ("X509/Prim.lean", "BOOLEAN TRUE accepted as 0x01",
     "  | [0xFF] => some true\n", "  | [0xFF] => some true\n  | [0x01] => some true\n"),
    ("X509/Prim.lean", "GeneralizedTime accepted before 2050",
     "if 2050 ≤ y then stamp y rest else none", "stamp y rest"),
    ("X509/Prim.lean", "February 29 in every year",
     "if m = 2 then (if isLeap y then 29 else 28)", "if m = 2 then 29"),
    ("X509/Sha256.lean", "one SHA-256 round constant wrong",
     "0x428a2f98", "0x428a2f99"),
    ("X509/Rsa.lean", "signature not required to be below the modulus",
     "decide (s < key.n) && decide", "decide"),
    ("X509/Rsa.lean", "padding block type 0x02 instead of 0x01",
     "((0x01 * 2 ^ (8 * ps)", "((0x02 * 2 ^ (8 * ps)"),
    ("X509/Host.lean", "wildcard allowed over a single remaining label (*.com)",
     "| [42] :: rest => 2 ≤ rest.length && rest.all labelOk", "| [42] :: rest => rest.all labelOk"),
    ("X509/Host.lean", "host labels not restricted to letters, digits and hyphens",
     "def labelOk (l : List Nat) : Bool := l ≠ [] && l.length ≤ 63 && l.all ldh",
     "def labelOk (l : List Nat) : Bool := l ≠ [] && l.length ≤ 63"),
    ("X509/Host.lean", "wildcard matching any number of labels",
     "h.tail == rest", "h.drop (h.length - rest.length) == rest"),
    ("X509/Cert.lean", "critical FALSE written out accepted",
     "  | .cons 0x30 [.prim 0x06 oid, .prim 0x01 [0xFF], .prim 0x04 v] =>",
     "  | .cons 0x30 [.prim 0x06 oid, .prim 0x01 [0x00], .prim 0x04 v] => if oidOk oid then some ⟨oid, false, v⟩ else none\n  | .cons 0x30 [.prim 0x06 oid, .prim 0x01 [0xFF], .prim 0x04 v] =>"),
    ("X509/Cert.lean", "the same extension allowed twice",
     "  if !distinct (exts.map (·.oid)) then none\n", ""),
    ("X509/Cert.lean", "unknown critical extensions ignored",
     "  if exts.any (fun e => e.critical && !understood e.oid) then none\n", ""),
    ("X509/Cert.lean", "inner and outer signature algorithms not compared",
     "if encode innerAlg = encode alg then", "if true then"),
    ("X509/Cert.lean", "OIDs not checked for padding",
     "if start && b == 0x80 then false else", "if false then false else"),
    ("X509/Chain.lean", "issuer not required to be a CA",
     "child.issuer == parent.subject && parent.isCA &&", "child.issuer == parent.subject &&"),
    ("X509/Chain.lean", "issuer name not compared",
     "child.issuer == parent.subject && parent.isCA &&", "parent.isCA &&"),
    ("X509/Chain.lean", "expiry not checked",
     "c.notBefore ≤ now && now ≤ c.notAfter", "c.notBefore ≤ now"),
    ("X509/Chain.lean", "path length off by one",
     "decide (i ≤ p + 1)", "decide (i ≤ p + 2)"),
    ("X509/Chain.lean", "keyCertSign not required of issuers",
     "parent.isCA && kuAllows parent 5 &&", "parent.isCA &&"),
    ("X509/Chain.lean", "leaf's extKeyUsage ignored",
     "kuAllows leaf 0 && ekuServer leaf", "kuAllows leaf 0"),
]


def run(cmd):
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)


def main():
    only = sys.argv[1:]
    results = []
    for i, (path, what, old, new) in enumerate(MUTANTS):
        if only and str(i) not in only:
            continue
        full = os.path.join(ROOT, path)
        original = open(full).read()
        if original.count(old) != 1:
            print(f"[{i}] {what}: pattern not found exactly once in {path}", flush=True)
            results.append((what, "BROKEN MUTANT"))
            continue
        try:
            open(full, "w").write(original.replace(old, new))
            b = run(["lake", "build"])
            if b.returncode != 0:
                errs = [l for l in b.stdout.splitlines() if l.startswith("error:") and ".lean:" in l]
                where = errs[0].split(": ", 1)[1].split(":")[0] if errs else "build"
                verdict = f"killed by a proof ({os.path.basename(where)})"
            elif run(["python3", "test/negative.py"]).returncode != 0:
                verdict = "killed by test/negative.py"
            elif run(["python3", "test/differential.py"]).returncode != 0:
                verdict = "killed by test/differential.py"
            else:
                verdict = "SURVIVED"
        finally:
            open(full, "w").write(original)
        print(f"[{i:2}] {what:58} {verdict}", flush=True)
        results.append((what, verdict))
    run(["lake", "build"])
    survived = [w for w, v in results if v in ("SURVIVED", "BROKEN MUTANT")]
    print(f"\n{len(results) - len(survived)}/{len(results)} mutants killed")
    sys.exit(1 if survived else 0)


if __name__ == "__main__":
    main()
