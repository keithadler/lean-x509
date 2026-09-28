import X509.Der
import X509.Sha256

/-!
# The primitive values inside a certificate

INTEGER, BOOLEAN, and the two time types, each read the DER way: one value, one encoding. The proofs
show the integer and boolean readers accept exactly what the matching writers produce, so equal values
always have equal bytes.
-/

namespace X509

/-! ## Non-negative INTEGER

X.509 serial numbers, path lengths and RSA moduli are never negative, so this reader refuses a negative
INTEGER outright. DER writes an integer in the fewest two's-complement bytes, which for a non-negative one
means: no leading `0x00` unless the next byte has its top bit set (else it would read as negative). -/

/-- The DER contents of a non-negative INTEGER. -/
def encodeUInt (n : Nat) : List Nat :=
  if n = 0 then [0]
  else match be n with
    | b :: bs => if b < 128 then b :: bs else 0 :: b :: bs
    | [] => [0]

/-- Reads the contents of a non-negative INTEGER, refusing a negative value, a redundant leading zero, and
empty contents. -/
def decodeUInt : List Nat → Option Nat
  | [] => none
  | [b] => if b < 128 then some b else none
  | b :: c :: rest =>
    if b < 128 ∧ ¬(b = 0 ∧ c < 128) ∧ (b :: c :: rest).all (· < 256) then some (ofBE (b :: c :: rest))
    else none

theorem ofBE_cons_zero (bs : List Nat) : ofBE (0 :: bs) = ofBE bs := by
  simp [ofBE]

theorem decodeUInt_encodeUInt (n : Nat) : decodeUInt (encodeUInt n) = some n := by
  unfold encodeUInt
  by_cases h : n = 0
  · subst h; simp [decodeUInt]
  · simp only [h, ite_false]
    have hofbe := ofBE_be n
    have hall := be_lt n
    have hhead := be_head n
    cases hb : be n with
    | nil => exact absurd hb (be_ne_nil h)
    | cons b bs =>
      rw [hb] at hofbe hall hhead
      have hb0 : b ≠ 0 := by simpa using hhead
      have hb256 : b < 256 := hall b (by simp)
      have hall' : (b :: bs).all (· < 256) = true := by simpa using hall
      by_cases hlt : b < 128
      · simp only [hlt, ite_true]
        cases bs with
        | nil => simp [decodeUInt, hlt]; simpa [ofBE] using hofbe
        | cons c cs =>
          simp only [decodeUInt, hlt, hb0, false_and, not_false_eq_true, hall', and_self, ite_true, hofbe]
      · simp only [hlt, ite_false]
        have hall0 : (0 :: b :: bs).all (· < 256) = true := by simp at hall' ⊢; exact hall'
        simp only [decodeUInt, show (0 : Nat) < 128 by omega, show ¬ b < 128 from hlt, and_false,
          not_false_eq_true, hall0, and_self, ite_true, ofBE_cons_zero, hofbe]

/-- Every integer the reader accepts is written exactly the way `encodeUInt` writes it. -/
theorem encodeUInt_decodeUInt {c : List Nat} {n : Nat} (h : decodeUInt c = some n) : c = encodeUInt n := by
  match c, h with
  | [b], h =>
    simp only [decodeUInt] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq] at h; subst h
      unfold encodeUInt
      by_cases h0 : b = 0
      · simp [h0]
      · simp only [h0, ite_false]
        have : be b = [b] := by
          rw [be_pos h0, show b / 256 = 0 by omega, be_zero, show b % 256 = b by omega]; rfl
        simp [this, hb]
    · simp at h
  | b :: c :: rest, h =>
    simp only [decodeUInt] at h
    split at h
    · rename_i hc
      obtain ⟨hb, hz, hall⟩ := hc
      simp only [Option.some.injEq] at h; subst h
      unfold encodeUInt
      by_cases hb0 : b = 0
      · subst hb0
        have hc128 : 128 ≤ c := by omega
        have hall' : (c :: rest).all (· < 256) = true := by simp at hall ⊢; exact hall
        have hbe := be_ofBE (c :: rest) hall' (by simp; omega)
        rw [ofBE_cons_zero]
        have hne : ofBE (c :: rest) ≠ 0 := ofBE_pos rest c (by omega)
        simp only [hne, ite_false, hbe, show ¬ c < 128 by omega]
      · have hbe := be_ofBE (b :: c :: rest) hall (by simpa using hb0)
        have hne : ofBE (b :: c :: rest) ≠ 0 := ofBE_pos (c :: rest) b hb0
        simp only [hne, ite_false, hbe, hb, ite_true]
    · simp at h

/-- One integer, one encoding. -/
theorem decodeUInt_unique {c₁ c₂ : List Nat} {n : Nat}
    (h₁ : decodeUInt c₁ = some n) (h₂ : decodeUInt c₂ = some n) : c₁ = c₂ := by
  rw [encodeUInt_decodeUInt h₁, encodeUInt_decodeUInt h₂]

/-! ## BOOLEAN

BER lets any non-zero byte mean TRUE; DER allows only `0xFF`. -/

def decodeBool : List Nat → Option Bool
  | [0xFF] => some true
  | [0x00] => some false
  | _ => none

def encodeBool (b : Bool) : List Nat := if b then [0xFF] else [0x00]

theorem decodeBool_iff (c : List Nat) (b : Bool) : decodeBool c = some b ↔ c = encodeBool b := by
  cases b <;> constructor <;> intro h <;>
    first
    | (subst h; rfl)
    | (unfold decodeBool at h; split at h <;> simp_all [encodeBool])

/-! ## Time

A validity date is kept as the number `YYYYMMDDHHMMSS`, so comparing numbers compares times. RFC 5280
§4.1.2.5 fixes the encoding: UTCTime (`YYMMDDHHMMSSZ`, years 1950 to 2049) for dates through 2049 and
GeneralizedTime (`YYYYMMDDHHMMSSZ`) from 2050 on, always in UTC, always with seconds and no fractions.
This reader accepts only that, so each date has one encoding. -/

/-- The value of ASCII decimal digits, or nothing if any byte is not a digit. -/
def digits (bs : List Nat) : Option Nat :=
  bs.foldl (fun acc b => acc.bind fun a => if 48 ≤ b ∧ b ≤ 57 then some (a * 10 + (b - 48)) else none) (some 0)

def isLeap (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def daysIn (y m : Nat) : Nat :=
  if m = 2 then (if isLeap y then 29 else 28)
  else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30 else 31

/-- Checks the month, day, hour, minute and second of `MMDDHHMMSS` and joins them to the year. -/
def stamp (y rest : Nat) : Option Nat :=
  let mo := rest / 100000000 % 100
  let d := rest / 1000000 % 100
  let h := rest / 10000 % 100
  let mi := rest / 100 % 100
  let s := rest % 100
  if 1 ≤ mo ∧ mo ≤ 12 ∧ 1 ≤ d ∧ d ≤ daysIn y mo ∧ h < 24 ∧ mi < 60 ∧ s < 60 then
    some (y * 10000000000 + rest)
  else none

/-- Reads a UTCTime (tag `0x17`) or GeneralizedTime (tag `0x18`) the way RFC 5280 requires. -/
def decodeTime (tag : Nat) (c : List Nat) : Option Nat :=
  if tag = 0x17 ∧ c.length = 13 ∧ c.getLast? = some 90 then do
    let yy ← digits (c.take 2)
    let rest ← digits ((c.drop 2).take 10)
    stamp (if yy < 50 then 2000 + yy else 1900 + yy) rest
  else if tag = 0x18 ∧ c.length = 15 ∧ c.getLast? = some 90 then do
    let y ← digits (c.take 4)
    let rest ← digits ((c.drop 4).take 10)
    if 2050 ≤ y then stamp y rest else none
  else none

/-- The two-digit years of UTCTime: `49` is 2049, `50` is 1950 (RFC 5280 §4.1.2.5.1). -/
theorem utc_window :
    decodeTime 0x17 (Sha256.ascii "491231235959Z") = some 20491231235959 ∧
    decodeTime 0x17 (Sha256.ascii "500101000000Z") = some 19500101000000 := by
  decide +kernel

/-- Dates through 2049 have only the UTCTime form: GeneralizedTime for them is refused. -/
theorem generalized_before_2050_refused :
    decodeTime 0x18 (Sha256.ascii "20261207043713Z") = none := by
  decide +kernel

/-- No February 29 in a year that is not a leap year, and no hour 24. -/
theorem impossible_dates_refused :
    decodeTime 0x17 (Sha256.ascii "270229000000Z") = none ∧
    decodeTime 0x17 (Sha256.ascii "280229000000Z") = some 20280229000000 ∧
    decodeTime 0x17 (Sha256.ascii "261207240000Z") = none := by
  decide +kernel

end X509
