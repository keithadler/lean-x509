import X509.Cert
import X509.Host

/-!
# Chain validation (RFC 5280 §6.1, for a TLS server)

A chain is the list a server presents: its own certificate first, then each issuer in turn. `Valid` says
in plain terms what it takes for such a chain to vouch for a host at a given time; `validate` is the
checker that runs. `validate_iff` proves they agree, and the theorems after it read facts straight off
`Valid`: every issuer is a CA, every certificate is current, every signature is over exactly the bytes
presented, the leaf names the host.

What this does not cover: revocation (CRLs, OCSP), name constraints and policy processing (a certificate
marking either critical is refused, since the decoder does not understand it), path building (the chain is
checked in the order given), and signature algorithms other than RSA with SHA-256. Names are compared byte
for byte, which is stricter than RFC 5280's case-folding comparison and matches what browsers do in
practice.
-/

namespace X509

/-- A trust anchor: a name and a key, nothing more (RFC 5280 §6.1.1 d). -/
structure Anchor where
  subject : Name
  key : Rsa.Key

/-- The anchor a self-signed root certificate stands for. -/
def Anchor.ofCert (c : Cert) : Option Anchor :=
  match c.key with
  | .rsa k => some ⟨c.subject, k⟩
  | .other _ => none

/-- The DER of `sha256WithRSAEncryption` with its NULL parameters. -/
def sha256WithRSAAlg : List Nat := [0x30, 0x0d, 0x06, 0x09] ++ Oid.sha256WithRSA ++ [0x05, 0x00]

/-- Does `key` sign `c`, with RSA and SHA-256, over `c.tbs`? -/
def signedBy (key : Rsa.Key) (c : Cert) : Bool :=
  c.sigAlg == sha256WithRSAAlg && c.sigBytes == Rsa.byteLen key.n && Rsa.verify key c.tbs c.signature

/-- keyUsage bit `i` (0 is digitalSignature, 5 is keyCertSign), or `true` if keyUsage is absent. -/
def kuAllows (c : Cert) (i : Nat) : Bool :=
  match c.keyUsage with
  | none => true
  | some bits => (bits.getD (i / 8) 0) >>> (7 - i % 8) % 2 == 1

/-- extKeyUsage allows TLS server authentication, or is absent. -/
def ekuServer (c : Cert) : Bool :=
  match c.eku with
  | none => true
  | some ps => ps.contains Oid.serverAuth || ps.contains Oid.anyExtendedKeyUsage

/-- `parent` issued `child`: the names chain, the parent is a CA allowed to sign certificates, and its key
signs the child. -/
def issues (parent child : Cert) : Bool :=
  child.issuer == parent.subject && parent.isCA && kuAllows parent 5 &&
    match parent.key with
    | .rsa k => signedBy k child
    | .other _ => false

def current (now : Nat) (c : Cert) : Bool := c.notBefore ≤ now && now ≤ c.notAfter

/-! ## The specification -/

/-- What it takes for `chain` to vouch for `host` at time `now`, given the trusted `anchors`. -/
structure Valid (anchors : List Anchor) (now : Nat) (host : List Nat) (chain : List Cert) : Prop where
  /-- The server presented at least one certificate; the first is the leaf. -/
  nonempty : chain ≠ []
  /-- Every certificate is v3 and inside its validity period. -/
  v3 : ∀ c ∈ chain, c.version = 2
  timely : ∀ c ∈ chain, c.notBefore ≤ now ∧ now ≤ c.notAfter
  /-- Each certificate is issued by the next one. -/
  linked : ∀ i (h : i + 1 < chain.length), issues chain[i + 1] chain[i] = true
  /-- A CA whose basicConstraints say `pathLenConstraint = p` has at most `p` intermediates below it. -/
  pathLen : ∀ i (h : i < chain.length) p, chain[i].pathLen = some p → i ≤ p + 1
  /-- The last certificate is signed by a trust anchor whose name is its issuer. -/
  anchored : ∀ last, chain.getLast? = some last →
    ∃ a ∈ anchors, a.subject = last.issuer ∧ signedBy a.key last = true
  /-- The leaf names the host, may sign (TLS 1.3 needs digitalSignature), and is for TLS servers. -/
  names : ∀ leaf, chain.head? = some leaf →
    (∃ d ∈ leaf.dnsNames, Host.nameMatches d host = true) ∧ kuAllows leaf 0 = true ∧ ekuServer leaf = true

/-! ## The checker -/

def linkedB : List Cert → Bool
  | a :: b :: rest => issues b a && linkedB (b :: rest)
  | _ => true

def pathLenB : Nat → List Cert → Bool
  | _, [] => true
  | i, c :: cs => (match c.pathLen with | some p => decide (i ≤ p + 1) | none => true) && pathLenB (i + 1) cs

def anchoredB (anchors : List Anchor) (chain : List Cert) : Bool :=
  match chain.getLast? with
  | some last => anchors.any fun a => a.subject == last.issuer && signedBy a.key last
  | none => true

def namesB (host : List Nat) (chain : List Cert) : Bool :=
  match chain.head? with
  | some leaf => leaf.dnsNames.any (Host.nameMatches · host) && kuAllows leaf 0 && ekuServer leaf
  | none => true

/-- Validates a presented chain for `host` at `now`. -/
def validate (anchors : List Anchor) (now : Nat) (host : List Nat) (chain : List Cert) : Bool :=
  !chain.isEmpty && chain.all (·.version == 2) && chain.all (current now) && linkedB chain &&
    pathLenB 0 chain && anchoredB anchors chain && namesB host chain

/-! ## The checker is the specification -/

theorem linkedB_iff : ∀ (l : List Cert),
    linkedB l = true ↔ ∀ i (h : i + 1 < l.length), issues l[i + 1] l[i] = true := by
  intro l
  induction l with
  | nil => simp [linkedB]
  | cons a l ih =>
    cases l with
    | nil => simp [linkedB]
    | cons b l =>
      simp only [linkedB, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hab, hrest⟩ i hi
        cases i with
        | zero => simpa using hab
        | succ i => exact hrest i (by simp at hi ⊢; omega)
      · intro h
        refine ⟨by simpa using h 0 (by simp), fun i hi => ?_⟩
        exact h (i + 1) (by simp at hi ⊢; omega)

theorem pathLenB_iff : ∀ (l : List Cert) (k : Nat),
    pathLenB k l = true ↔ ∀ i (h : i < l.length) p, l[i].pathLen = some p → k + i ≤ p + 1 := by
  intro l
  induction l with
  | nil => simp [pathLenB]
  | cons c l ih =>
    intro k
    simp only [pathLenB, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hc, hrest⟩ i hi p hp
      cases i with
      | zero => simp at hp; rw [hp] at hc; simpa using hc
      | succ i => have := hrest i (by simp at hi; omega) p (by simpa using hp); omega
    · intro h
      refine ⟨?_, fun i hi p hp => ?_⟩
      · split
        · rename_i p hp; have := h 0 (by simp) p (by simpa using hp); simpa using this
        · rfl
      · have := h (i + 1) (by simp; omega) p (by simpa using hp); omega

theorem validate_iff (anchors : List Anchor) (now : Nat) (host : List Nat) (chain : List Cert) :
    validate anchors now host chain = true ↔ Valid anchors now host chain := by
  simp only [validate, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
    beq_iff_eq, current, decide_eq_true_eq, linkedB_iff, pathLenB_iff, Nat.zero_add]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨hne, hv⟩, ht⟩, hl⟩, hp⟩, ha⟩, hn⟩
    refine ⟨hne, hv, ht, hl, hp, ?_, ?_⟩
    · intro last hlast
      simp only [anchoredB, hlast, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at ha
      exact ha
    · intro leaf hleaf
      simp only [namesB, hleaf, Bool.and_eq_true, List.any_eq_true] at hn
      exact ⟨hn.1.1, hn.1.2, hn.2⟩
  · rintro ⟨hne, hv, ht, hl, hp, ha, hn⟩
    refine ⟨⟨⟨⟨⟨⟨hne, hv⟩, ht⟩, hl⟩, hp⟩, ?_⟩, ?_⟩
    · unfold anchoredB; split
      · rename_i last hlast
        simpa only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] using ha last hlast
      · rfl
    · unfold namesB; split
      · rename_i leaf hleaf
        obtain ⟨h1, h2, h3⟩ := hn leaf hleaf
        simp only [Bool.and_eq_true, List.any_eq_true]; exact ⟨⟨h1, h2⟩, h3⟩
      · rfl

/-! ## What a valid chain guarantees -/

/-- Every certificate after the leaf is a CA: a server's own certificate can never be used to issue
another (the basicConstraints check that some clients skipped in 2002). -/
theorem issuers_are_CAs {anchors now host chain} (hv : Valid anchors now host chain)
    (i : Nat) (hi : 0 < i) (h : i < chain.length) : chain[i].isCA = true := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have := hv.linked j h
  simp only [issues, Bool.and_eq_true] at this
  exact this.1.1.2

/-- Every issuer is allowed to sign certificates (keyUsage keyCertSign, when keyUsage is present). -/
theorem issuers_may_sign {anchors now host chain} (hv : Valid anchors now host chain)
    (i : Nat) (h : i + 1 < chain.length) : kuAllows chain[i + 1] 5 = true := by
  have := hv.linked i h
  simp only [issues, Bool.and_eq_true] at this
  exact this.1.2

/-- Each certificate names the next one as its issuer. -/
theorem names_chain {anchors now host chain} (hv : Valid anchors now host chain)
    (i : Nat) (h : i + 1 < chain.length) : chain[i].issuer = chain[i + 1].subject := by
  have := hv.linked i h
  simp only [issues, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1.1.1

/-- Each certificate carries an RSA signature, by its issuer's key, over its own `tbs` bytes. -/
theorem signatures_verify {anchors now host chain} (hv : Valid anchors now host chain)
    (i : Nat) (h : i + 1 < chain.length) :
    ∃ k, chain[i + 1].key = .rsa k ∧ Rsa.verify k chain[i].tbs chain[i].signature = true := by
  have := hv.linked i h
  simp only [issues, Bool.and_eq_true] at this
  obtain ⟨-, hk⟩ := this
  split at hk
  · rename_i k hkey
    simp only [signedBy, Bool.and_eq_true] at hk
    exact ⟨k, hkey, hk.2⟩
  · simp at hk

/-- No certificate in a valid chain is expired or not yet valid. -/
theorem all_current {anchors now host chain} (hv : Valid anchors now host chain) :
    ∀ c ∈ chain, c.notBefore ≤ now ∧ now ≤ c.notAfter := hv.timely

/-- The path length constraint in plain terms: a CA at position `i` (the leaf is position 0) with
`pathLenConstraint = p` has `i - 1 ≤ p` intermediates between it and the leaf. -/
theorem path_length {anchors now host chain} (hv : Valid anchors now host chain)
    (i : Nat) (h : i < chain.length) (p : Nat) (hp : chain[i].pathLen = some p) : i - 1 ≤ p := by
  have := hv.pathLen i h p hp; omega

/-- The host the chain is valid for is a well-formed DNS name with no NUL byte in it. -/
theorem host_has_no_nul {anchors now host chain} (hv : Valid anchors now host chain) : 0 ∉ host := by
  cases hc : chain with
  | nil => exact absurd hc hv.nonempty
  | cons leaf rest =>
    obtain ⟨⟨d, -, hd⟩, -⟩ := hv.names leaf (by simp [hc])
    exact Host.names_no_nul hd

end X509
