import X509.Chain
import X509.Data

/-!
# A real chain, checked by Lean's kernel

The chain keithadler.github.io served on 2026-09-27, captured with `openssl s_client -showcerts`, and ISRG
Root X1 from the macOS trust store (`certs/`):

    *.github.io  ←  Let's Encrypt YR1  ←  ISRG Root YR  ←  ISRG Root X1 (trust anchor)

All RSA with SHA-256: a 2048-bit leaf and intermediate, 4096-bit roots. Every theorem here is proved by
`decide +kernel`, which hands the whole computation to Lean's kernel: DER parsing, SHA-256 of each
`tbsCertificate`, the RSA modular exponentiation, name chaining, dates and host-name matching. No compiled
code is trusted, and Tenet, an independent Lean kernel, checks the same terms again.
-/

namespace X509.Real

/-- The chain as presented, decoded. -/
def chain : Option (List Cert) := [Data.leaf, Data.yr1, Data.rootYR].mapM decodeCert

/-- The one trust anchor: ISRG Root X1's name and key, read from its own certificate. -/
def anchors : List Anchor := ((decodeCert Data.isrgX1).bind Anchor.ofCert).toList

/-- 2026-09-27 12:00:00 UTC. -/
def now : Nat := 20260927120000

def host (s : String) : List Nat := Sha256.ascii s

/-- The chain keithadler.github.io serves is valid for keithadler.github.io today, through the
certificate's `*.github.io` wildcard. -/
theorem keithadler_github_io :
    chain.map (validate anchors now (host "keithadler.github.io")) = some true := by
  decide +kernel

/-- A wildcard covers one label, not two: the same chain does not vouch for a host one level deeper. -/
theorem not_two_labels_deep :
    chain.map (validate anchors now (host "x.keithadler.github.io")) = some false := by
  decide +kernel

/-- It does not vouch for a host the certificate does not name. -/
theorem not_evil_com : chain.map (validate anchors now (host "evil.com")) = some false := by
  decide +kernel

/-- It stops being valid when the leaf expires, at 23:38:01 UTC on 2026-10-31. -/
theorem expires :
    chain.map (validate anchors 20261031233802 (host "keithadler.github.io")) = some false := by
  decide +kernel

/-- The same statement in terms of the specification: there is a decoded chain, and it is `Valid`. -/
theorem keithadler_github_io_valid :
    ∃ cs, chain = some cs ∧ Valid anchors now (host "keithadler.github.io") cs := by
  have hk := keithadler_github_io
  cases h : chain with
  | none => rw [h] at hk; simp at hk
  | some cs => rw [h] at hk; exact ⟨cs, rfl, (validate_iff _ _ _ _).mp (by simpa using hk)⟩

end X509.Real
