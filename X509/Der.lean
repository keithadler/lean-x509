/-!
# DER, the byte layer of X.509

Every X.509 certificate is a tree of tag-length-value triples written in DER, the Distinguished Encoding
Rules of X.690. "Distinguished" is the point: each value has exactly one encoding, so the bytes a CA signs
and the certificate a client reads cannot disagree. Parsers that accept more than DER (a long-form length
where a short one fits, a length with leading zero bytes, the indefinite length of BER) break that, and
two different byte strings then read as the same certificate.

This file defines the tree, the encoder and the parser, and proves:

* `parse_encode`: the parser reads back every tree the encoder writes;
* `encode_parse`: every byte string the parser accepts is exactly the encoding of what it returns;
* `der_unique`: so two byte strings that parse to the same tree are the same byte string.

Bytes are natural numbers. The parser checks `< 256` wherever a byte's value matters.
-/

namespace X509

/-- A DER tree. `tag` is the whole identifier octet; bit 6 (`0x20`) says whether the node is constructed. -/
inductive Node where
  | prim (tag : Nat) (content : List Nat)
  | cons (tag : Nat) (children : List Node)
  deriving Repr, Inhabited

namespace Node

def tag : Node → Nat
  | prim t _ => t
  | cons t _ => t

end Node

/-! ## Lengths -/

/-- The value of big-endian bytes. -/
def ofBE (bs : List Nat) : Nat := bs.foldl (fun a b => a * 256 + b) 0

/-- `be` with a bound on the number of steps, so that Lean's kernel can run it (`n` steps is plenty). -/
def beF : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else beF f (n / 256) ++ [n % 256]

/-- The shortest big-endian bytes of `n`: none for zero, and never a leading zero byte. -/
def be (n : Nat) : List Nat := beF n n

/-- The DER length octets: one byte below 128, otherwise `0x80 + k` followed by the `k` bytes of the length. -/
def encodeLen (n : Nat) : List Nat :=
  if n < 128 then [n] else (128 + (be n).length) :: be n

/-- Reads the length octets. Rejects the indefinite form `0x80`, the reserved `0xFF`, a long form with a
leading zero byte, and a long form for a length that fits in one byte. -/
def parseLen : List Nat → Option (Nat × List Nat)
  | [] => none
  | b :: rest =>
    if b < 128 then some (b, rest)
    else if 128 < b ∧ b < 255 then
      let c := b - 128
      let bs := rest.take c
      if bs.length = c ∧ bs.all (· < 256) ∧ bs.head? ≠ some 0 ∧ 128 ≤ ofBE bs then
        some (ofBE bs, rest.drop c)
      else none
    else none

/-! ## Trees -/

mutual
/-- The DER encoding of a node: tag, length, contents. -/
def encode : Node → List Nat
  | .prim t c => t :: encodeLen c.length ++ c
  | .cons t cs => t :: encodeLen (encodeSeq cs).length ++ encodeSeq cs
/-- The encodings of a list of nodes, one after the other. -/
def encodeSeq : List Node → List Nat
  | [] => []
  | n :: ns => encode n ++ encodeSeq ns
end

/-- Tag octets this parser accepts: one byte, not the `0x1F` escape to a multi-byte tag number. -/
def tagOk (t : Nat) : Bool := t < 256 && t % 32 != 31

/-- Is the constructed bit set? -/
def constructed (t : Nat) : Bool := t / 32 % 2 == 1

/-- Parses a whole byte string as a sequence of nodes. `fuel` bounds the work; `bs.length` is always enough
(`parse` below passes exactly that). Every node's contents must be read to the last byte. -/
def parseSeq : Nat → List Nat → Option (List Node)
  | _, [] => some []
  | 0, _ :: _ => none
  | f + 1, t :: rest =>
    if tagOk t then
      match parseLen rest with
      | none => none
      | some (n, rest') =>
        if n ≤ rest'.length then
          let body := rest'.take n
          let node : Option Node :=
            if constructed t then (parseSeq f body).map (Node.cons t) else some (Node.prim t body)
          match node, parseSeq f (rest'.drop n) with
          | some x, some xs => some (x :: xs)
          | _, _ => none
        else none
    else none

/-- Parses exactly one DER node that fills the whole input: trailing bytes are an error. -/
def parse (bs : List Nat) : Option Node :=
  match parseSeq bs.length bs with
  | some [x] => some x
  | _ => none

/-! ## Well-formed trees

The encoder writes any tree, but only some trees can come back: the tag has to be a single-byte tag whose
constructed bit matches the node, and a length has to fit in the 126 bytes DER allows (so any length below
2¹⁰⁰⁸, more bytes than there are atoms in the universe). -/

def lenOk (n : Nat) : Bool := n < 256 ^ 126

mutual
def wf : Node → Bool
  | .prim t c => tagOk t && !constructed t && lenOk c.length
  | .cons t cs => tagOk t && constructed t && wfSeq cs && lenOk (encodeSeq cs).length
def wfSeq : List Node → Bool
  | [] => true
  | n :: ns => wf n && wfSeq ns
end

/-! ## Proofs about lengths -/

/-- Induction that adds bytes at the end, the way `ofBE` reads them. -/
theorem snoc_induction {motive : List Nat → Prop} (nil : motive [])
    (snoc : ∀ bs b, motive bs → motive (bs ++ [b])) (bs : List Nat) : motive bs := by
  rw [← List.reverse_reverse bs]
  induction bs.reverse with
  | nil => exact nil
  | cons b r ih => rw [List.reverse_cons]; exact snoc _ _ ih

theorem ofBE_append (bs : List Nat) (b : Nat) : ofBE (bs ++ [b]) = ofBE bs * 256 + b := by
  simp [ofBE, List.foldl_append]

theorem beF_fuel : ∀ (f g n : Nat), n ≤ f → n ≤ g → beF f n = beF g n := by
  intro f
  induction f with
  | zero => intro g n hf _; have : n = 0 := by omega
            subst this; cases g <;> simp [beF]
  | succ f ih =>
    intro g n hf hg
    cases g with
    | zero => have : n = 0 := by omega
              subst this; simp [beF]
    | succ g =>
      by_cases h : n = 0
      · simp [beF, h]
      · simp only [beF, h, ite_false]; rw [ih g (n / 256) (by omega) (by omega)]

theorem be_zero : be 0 = [] := by simp [be, beF]

theorem be_pos {n : Nat} (h : n ≠ 0) : be n = be (n / 256) ++ [n % 256] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [be, beF, Nat.add_one_ne_zero, ite_false]
  rw [beF_fuel m ((m + 1) / 256) ((m + 1) / 256) (by omega) (by omega)]

theorem ofBE_be (n : Nat) : ofBE (be n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n = 0
    · subst h; simp [be_zero, ofBE]
    · rw [be_pos h, ofBE_append, ih (n / 256) (by omega)]; omega

theorem be_lt (n : Nat) : ∀ x ∈ be n, x < 256 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n = 0
    · subst h; simp [be_zero]
    · rw [be_pos h]; intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact ih _ (by omega) x hx
      · omega

theorem be_head (n : Nat) : (be n).head? ≠ some 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n = 0
    · subst h; simp [be_zero]
    · rw [be_pos h]
      by_cases h2 : n / 256 = 0
      · rw [h2, be_zero]; simp; omega
      · have := ih (n / 256) (by omega)
        cases hb : be (n / 256) with
        | nil => rw [be_pos h2] at hb; simp at hb
        | cons x xs => rw [hb] at this; simpa using this

theorem be_length_le (n k : Nat) (h : n < 256 ^ k) : (be n).length ≤ k := by
  induction k generalizing n with
  | zero => simp at h; subst h; simp [be_zero]
  | succ k ih =>
    by_cases hn : n = 0
    · subst hn; simp [be_zero]
    · rw [be_pos hn]; simp only [List.length_append, List.length_singleton]
      have : n / 256 < 256 ^ k := by rw [Nat.pow_succ] at h; omega
      have := ih _ this; omega

theorem be_ne_nil {n : Nat} (h : n ≠ 0) : be n ≠ [] := by
  rw [be_pos h]; simp

theorem ofBE_pos : ∀ (bs : List Nat) (x : Nat), x ≠ 0 → ofBE (x :: bs) ≠ 0 := by
  intro bs
  induction bs using snoc_induction with
  | nil => intro x hx; simpa [ofBE] using hx
  | snoc bs b ih =>
    intro x hx
    rw [← List.cons_append, ofBE_append]
    have := ih x hx; omega

/-- Canonical big-endian bytes come back unchanged: `be` is the only encoding `ofBE` inverts. -/
theorem be_ofBE : ∀ (bs : List Nat), bs.all (· < 256) = true → bs.head? ≠ some 0 → be (ofBE bs) = bs := by
  intro bs
  induction bs using snoc_induction with
  | nil => intro _ _; simp [ofBE, be_zero]
  | snoc bs b ih =>
    intro hall hhead
    simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hall
    rw [ofBE_append]
    cases bs with
    | nil =>
      have hb : b ≠ 0 := by simpa using hhead
      have hb2 : b / 256 = 0 := by omega
      simp only [ofBE, List.foldl, Nat.zero_mul, Nat.zero_add, List.nil_append]
      rw [be_pos hb, hb2, be_zero]; simp; omega
    | cons x xs =>
      have hx : x ≠ 0 := by simpa using hhead
      have hpos := ofBE_pos xs x hx
      have hne : ofBE (x :: xs) * 256 + b ≠ 0 := by omega
      rw [be_pos hne]
      have h1 : (ofBE (x :: xs) * 256 + b) / 256 = ofBE (x :: xs) := by omega
      have h2 : (ofBE (x :: xs) * 256 + b) % 256 = b := by omega
      rw [h1, h2, ih hall.1 hhead]

theorem parseLen_encodeLen (n : Nat) (r : List Nat) (h : lenOk n = true) :
    parseLen (encodeLen n ++ r) = some (n, r) := by
  unfold encodeLen
  by_cases hn : n < 128
  · simp [hn, parseLen]
  · simp only [hn, ite_false, List.cons_append, parseLen]
    have hne : n ≠ 0 := by omega
    have hlen := be_length_le n 126 (by simpa [lenOk] using h)
    have hpos : (be n).length ≠ 0 := by
      have := be_ne_nil hne; cases hb : be n <;> simp_all
    have hall : (be n).all (· < 256) = true := by
      simp only [List.all_eq_true, decide_eq_true_eq]; exact be_lt n
    simp only [show ¬ (128 + (be n).length < 128) by omega, ite_false,
      show 128 < 128 + (be n).length ∧ 128 + (be n).length < 255 from ⟨by omega, by omega⟩, ite_true,
      show 128 + (be n).length - 128 = (be n).length by omega, List.take_left', List.drop_left',
      hall, be_head n, ofBE_be, true_and, ne_eq, not_false_eq_true]
    simp; omega

/-- Every length the parser accepts is written exactly the way the encoder writes it. -/
theorem encodeLen_parseLen {bs r : List Nat} {n : Nat} (h : parseLen bs = some (n, r)) :
    bs = encodeLen n ++ r := by
  match bs, h with
  | b :: rest, h =>
    unfold parseLen at h
    by_cases h1 : b < 128
    · simp [h1] at h; obtain ⟨rfl, rfl⟩ := h; simp [encodeLen, h1]
    · simp only [h1, ite_false] at h
      by_cases h2 : 128 < b ∧ b < 255
      · simp only [h2, and_self, ite_true] at h
        split at h
        · rename_i hc
          obtain ⟨hl, hall, hhead, hbig⟩ := hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hbe := be_ofBE _ hall hhead
          unfold encodeLen
          simp only [show ¬ ofBE (rest.take (b - 128)) < 128 by omega, ite_false, hbe, hl,
            List.cons_append, List.cons.injEq]
          exact ⟨by omega, (List.take_append_drop _ _).symm⟩
        · simp at h
      · simp [h2] at h

/-! ## Proofs about trees -/

theorem encodeSeq_append (xs ys : List Node) : encodeSeq (xs ++ ys) = encodeSeq xs ++ encodeSeq ys := by
  induction xs with
  | nil => simp [encodeSeq]
  | cons x xs ih => simp [encodeSeq, ih]

/-- Every byte string the parser accepts is exactly the encoding of the nodes it returns. -/
theorem encodeSeq_parseSeq : ∀ (f : Nat) (bs : List Nat) (ns : List Node),
    parseSeq f bs = some ns → bs = encodeSeq ns := by
  intro f
  induction f with
  | zero =>
    intro bs ns h
    cases bs with
    | nil => simp [parseSeq] at h; subst h; rfl
    | cons _ _ => simp [parseSeq] at h
  | succ f ih =>
    intro bs ns h
    cases bs with
    | nil => simp [parseSeq] at h; subst h; rfl
    | cons t rest =>
      simp only [parseSeq] at h
      split at h
      · split at h
        · simp at h
        · rename_i n rest' hlen
          have hrest := encodeLen_parseLen hlen
          split at h
          · rename_i hn
            split at h
            · rename_i x xs hx hxs
              simp only [Option.some.injEq] at h; subst h
              have htail := ih _ _ hxs
              have hbody : (rest'.take n).length = n := by simp; omega
              split at hx
              · simp only [Option.map_eq_some_iff] at hx
                obtain ⟨cs, hcs, rfl⟩ := hx
                have hb := ih _ _ hcs
                simp only [encodeSeq, encode, List.cons_append, List.append_assoc, hrest]
                rw [← hb, hbody, ← htail, List.take_append_drop]
              · simp only [Option.some.injEq] at hx; subst hx
                simp only [encodeSeq, encode, List.cons_append, List.append_assoc, hrest, hbody]
                rw [← htail, List.take_append_drop]
            · simp at h
          · simp at h
      · simp at h

theorem length_encodeLen_pos (n : Nat) : 1 ≤ (encodeLen n).length := by
  unfold encodeLen; split <;> simp

theorem length_encode_pos (x : Node) : 2 ≤ (encode x).length := by
  cases x with
  | prim t c => have := length_encodeLen_pos c.length; simp only [encode, List.length_cons, List.length_append]; omega
  | cons t cs =>
    have := length_encodeLen_pos (encodeSeq cs).length
    simp only [encode, List.length_cons, List.length_append]; omega

/-- The parser reads back every well-formed sequence the encoder writes, given enough fuel. -/
theorem parseSeq_encodeSeq : ∀ (f : Nat) (ns : List Node),
    wfSeq ns = true → (encodeSeq ns).length ≤ f → parseSeq f (encodeSeq ns) = some ns := by
  intro f
  induction f with
  | zero =>
    intro ns _ hl
    cases ns with
    | nil => simp [encodeSeq, parseSeq]
    | cons x xs =>
      have := length_encode_pos x
      simp only [encodeSeq, List.length_append] at hl; omega
  | succ f ih =>
    intro ns hwf hl
    cases ns with
    | nil => simp [encodeSeq, parseSeq]
    | cons x xs =>
      simp only [wfSeq, Bool.and_eq_true] at hwf
      obtain ⟨hx, hxs⟩ := hwf
      have hxl := length_encode_pos x
      cases x with
      | prim t c =>
        simp only [wf, Bool.and_eq_true, Bool.not_eq_true'] at hx
        obtain ⟨⟨ht, hc⟩, hlen⟩ := hx
        simp only [encodeSeq, encode, List.cons_append, List.append_assoc, parseSeq, ht, ite_true,
          parseLen_encodeLen _ _ hlen]
        simp only [List.length_append, Nat.le_add_right, ite_true]
        simp only [List.take_left', List.drop_left', hc, Bool.false_eq_true, ite_false]
        simp only [encodeSeq, encode, List.length_cons, List.length_append] at hl
        rw [ih xs hxs (by omega)]
      | cons t cs =>
        simp only [wf, Bool.and_eq_true] at hx
        obtain ⟨⟨⟨ht, hc⟩, hcs⟩, hlen⟩ := hx
        simp only [encodeSeq, encode, List.cons_append, List.append_assoc, parseSeq, ht, ite_true,
          parseLen_encodeLen _ _ hlen]
        simp only [List.length_append, Nat.le_add_right, ite_true]
        simp only [List.take_left', List.drop_left', hc, ite_true]
        simp only [encodeSeq, encode, List.length_cons, List.length_append] at hl
        rw [ih cs hcs (by omega), ih xs hxs (by omega)]
        rfl

/-! ## The headline theorems -/

/-- The parser reads back every well-formed tree the encoder writes. -/
theorem parse_encode (x : Node) (h : wf x = true) : parse (encode x) = some x := by
  have hs : wfSeq [x] = true := by simp [wfSeq, h]
  have := parseSeq_encodeSeq (encode x).length [x] hs (by simp [encodeSeq])
  simp only [encodeSeq, List.append_nil] at this
  simp [parse, this]

/-- Every byte string the parser accepts is exactly the encoding of the tree it returns. There is no
second way to write it: no long-form length where a short one fits, no leading zero bytes in a length, no
indefinite length, no trailing bytes. -/
theorem encode_parse {bs : List Nat} {x : Node} (h : parse bs = some x) : bs = encode x := by
  unfold parse at h
  split at h
  · rename_i y hy
    simp only [Option.some.injEq] at h; subst h
    have := encodeSeq_parseSeq _ _ _ hy
    simpa [encodeSeq] using this
  · simp at h

/-- DER is distinguished: two byte strings that parse to the same tree are the same byte string. -/
theorem der_unique {bs₁ bs₂ : List Nat} {x : Node} (h₁ : parse bs₁ = some x) (h₂ : parse bs₂ = some x) :
    bs₁ = bs₂ := by
  rw [encode_parse h₁, encode_parse h₂]

/-- A parsed tree is always one the encoder can write back and the parser read again. -/
theorem parse_wf {bs : List Nat} {x : Node} (h : parse bs = some x) : parse (encode x) = some x := by
  rw [← encode_parse h]; exact h

/-! ## Refusals, checked by the kernel

The theorems above say the parser accepts exactly the DER encodings. These are the classic ways of
writing a value wrong, each refused. -/

/-- A long-form length (`0x81 0x01`) where one byte (`0x01`) fits. -/
theorem refuses_long_form : (parse [0x02, 0x81, 0x01, 0x05]).isNone = true := by decide +kernel

/-- A length with a leading zero byte. -/
theorem refuses_zero_padded_length : (parse [0x02, 0x82, 0x00, 0x01, 0x05]).isNone = true := by
  decide +kernel

/-- BER's indefinite length, `0x80`, ended by two zero bytes. -/
theorem refuses_indefinite : (parse [0x30, 0x80, 0x02, 0x01, 0x05, 0x00, 0x00]).isNone = true := by
  decide +kernel

/-- A byte after the value. -/
theorem refuses_trailing : (parse [0x02, 0x01, 0x05, 0x00]).isNone = true := by decide +kernel

/-- The reserved length octet `0xFF`. -/
theorem refuses_reserved_length : (parse ([0x04, 0xFF] ++ List.replicate 127 1)).isNone = true := by
  decide +kernel

/-- The escape `0x1F` that starts a multi-byte tag number is never read as a tag of its own. -/
theorem refuses_tag_escape : (parse [0x1F, 0x01, 0x05]).isNone = true := by decide +kernel

/-- The same value written the one right way is read. -/
theorem accepts_der : (parse [0x02, 0x01, 0x05]).isSome = true := by decide +kernel

end X509
