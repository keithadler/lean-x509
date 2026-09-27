import X509.Sha256

/-!
# RSA signatures, PKCS #1 v1.5 with SHA-256 (RFC 8017 §8.2.2)

Verification raises the signature to the public exponent modulo `n` and compares the result with the one
block a correct signer produces:

    0x00 0x01 0xFF … 0xFF 0x00 ‖ DigestInfo(SHA-256) ‖ H(m)

It does not parse that block. A verifier that reads the padding, finds the digest and ignores what follows
accepts forged signatures when the exponent is small (Bleichenbacher, 2006). Comparing the whole block as
one number leaves no bytes unread: `verify_iff` says the check passes exactly when `sᵉ mod n` equals the
one expected block.
-/

namespace X509.Rsa

/-- `b ^ e % m` by square-and-multiply over the bits of `e`; `fuel` counts bits. -/
def powMod (m : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1 % m
  | f + 1, b, e =>
    if e = 0 then 1 % m
    else
      let r := powMod m f (b * b % m) (e / 2)
      if e % 2 = 1 then b * r % m else r

/-- The number of bytes of `n`. -/
def byteLen (n : Nat) : Nat := (Nat.log2 n + 8) / 8

/-- The DER prefix of `DigestInfo` for SHA-256 (RFC 8017 §9.2, note 1). -/
def sha256Prefix : List Nat :=
  [0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00,
   0x04, 0x20]

/-- The one encoded message a correct signer of `msg` produces for a `k`-byte modulus, as a number. The
leading `0x00` byte adds nothing to the value, so the number is `0x01FF…FF00 ‖ T`. -/
def expected (k : Nat) (msg : List Nat) : Nat :=
  let t := sha256Prefix.foldl (fun a b => a * 256 + b) 0 * 2 ^ 256 + Sha256.hashNat msg
  let tLen := sha256Prefix.length + 32
  let ps := k - tLen - 3
  ((0x01 * 2 ^ (8 * ps) + (2 ^ (8 * ps) - 1)) * 256) * 2 ^ (8 * tLen) + t

/-- An RSA public key. -/
structure Key where
  n : Nat
  e : Nat
  deriving Repr, DecidableEq

/-- Does `s` sign `msg` under `key`? The signature has to be a number below the modulus, the modulus long
enough to hold the padding (at least 11 bytes of it), and `sᵉ mod n` the expected block. -/
def verify (key : Key) (msg : List Nat) (s : Nat) : Bool :=
  let k := byteLen key.n
  decide (s < key.n) && decide (sha256Prefix.length + 32 + 11 ≤ k) &&
    powMod key.n (Nat.log2 key.e + 1) s key.e == expected k msg

theorem powMod_eq : ∀ (f m b e : Nat), e < 2 ^ f → powMod m f b e = b ^ e % m := by
  intro f
  induction f with
  | zero => intro m b e h; simp at h; subst h; simp [powMod]
  | succ f ih =>
    intro m b e h
    simp only [powMod]
    by_cases he : e = 0
    · subst he; simp
    · simp only [he, if_false]
      rw [ih m (b * b % m) (e / 2) (by rw [Nat.pow_succ] at h; omega)]
      rw [← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      have hdiv := Nat.div_add_mod e 2
      by_cases hodd : e % 2 = 1
      · simp only [hodd, if_true]
        conv => rhs; rw [← hdiv, hodd]
        rw [Nat.pow_add, Nat.pow_one, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_comm, Nat.mul_comm 2]
      · have h0 : e % 2 = 0 := by omega
        simp only [hodd, if_false]
        conv => rhs; rw [← hdiv, h0]
        rw [Nat.add_zero, Nat.mul_comm 2]

/-- The check is the whole of the PKCS #1 v1.5 condition and nothing less: `s` below `n`, and `sᵉ mod n`
equal to the single block a correct signer makes. -/
theorem verify_iff (key : Key) (msg : List Nat) (s : Nat) :
    verify key msg s = true ↔
      s < key.n ∧ sha256Prefix.length + 32 + 11 ≤ byteLen key.n ∧
        s ^ key.e % key.n = expected (byteLen key.n) msg := by
  have hlog : key.e < 2 ^ (Nat.log2 key.e + 1) := Nat.lt_log2_self
  simp [verify, powMod_eq _ _ _ _ hlog, and_assoc]

end X509.Rsa
