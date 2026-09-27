import X509.Sha256

/-!
# Host names (RFC 6125, RFC 9525)

A certificate names the hosts it is for in subjectAltName dNSName entries. The rules this matcher keeps:

* comparison ignores ASCII case and nothing else;
* every label of the host is 1 to 63 letters, digits or hyphens, so no NUL, no dot inside a label,
  no empty label;
* a wildcard is only ever the whole leftmost label, `*`, and stands for exactly one label of the host;
* a wildcard needs at least two labels after it, so `*.com` names nothing.

The theorems at the end say what a match means in those terms.
-/

namespace X509.Host

/-- ASCII lower case. -/
def lower (c : Nat) : Nat := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

/-- A letter, digit or hyphen, in lower case. -/
def ldh (c : Nat) : Bool := (97 ≤ c && c ≤ 122) || (48 ≤ c && c ≤ 57) || c == 45

/-- Splits on dots. -/
def split : List Nat → List (List Nat)
  | [] => [[]]
  | c :: cs =>
    match split cs with
    | [] => [[c]]
    | l :: ls => if c = 46 then [] :: l :: ls else (c :: l) :: ls

/-- Joins labels with dots. -/
def join : List (List Nat) → List Nat
  | [] => []
  | [l] => l
  | l :: ls => l ++ 46 :: join ls

def labelOk (l : List Nat) : Bool := l ≠ [] && l.length ≤ 63 && l.all ldh

/-- A host name this matcher will consider: at least two labels, each well formed. -/
def hostOk (ls : List (List Nat)) : Bool := 2 ≤ ls.length && ls.all labelOk

/-- Does the dNSName `pat` name the host `host`? -/
def nameMatches (pat host : List Nat) : Bool :=
  let h := split (host.map lower)
  let p := split (pat.map lower)
  hostOk h &&
    match p with
    | [42] :: rest => 2 ≤ rest.length && rest.all labelOk && h.tail == rest
    | _ => p == h

/-! ## What a match means -/

theorem split_ne_nil (s : List Nat) : split s ≠ [] := by
  cases s with
  | nil => simp [split]
  | cons c cs => simp only [split]; split <;> (try split) <;> simp

/-- Splitting and joining again gives back the same string. -/
theorem join_split (s : List Nat) : join (split s) = s := by
  induction s with
  | nil => rfl
  | cons c cs ih =>
    simp only [split]
    split
    · rename_i h; exact absurd h (split_ne_nil cs)
    · rename_i l ls h
      rw [h] at ih
      split
      · rename_i hc; subst hc
        cases ls with
        | nil => simp [join] at ih ⊢; exact ih
        | cons l' ls' => simp [join] at ih ⊢; exact ih
      · cases ls with
        | nil => simp [join] at ih ⊢; exact ih
        | cons l' ls' => simp [join] at ih ⊢; exact ih

theorem split_no_dot : ∀ (s : List Nat) (l : List Nat), l ∈ split s → 46 ∉ l := by
  intro s
  induction s with
  | nil => simp [split]
  | cons c cs ih =>
    intro l hl
    simp only [split] at hl
    split at hl
    · rename_i h; exact absurd h (split_ne_nil cs)
    · rename_i l' ls h
      split at hl
      · simp only [List.mem_cons] at hl
        rcases hl with rfl | rfl | hl
        · simp
        · exact ih _ (by rw [h]; simp)
        · exact ih _ (by rw [h]; simp [hl])
      · rename_i hc
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl
        · simp only [List.mem_cons, not_or]; exact ⟨Ne.symm hc, ih _ (by rw [h]; simp)⟩
        · exact ih _ (by rw [h]; simp [hl])

theorem ldh_ne_zero {c : Nat} (h : ldh c = true) : c ≠ 0 := by
  simp [ldh] at h; omega

theorem ldh_ne_dot {c : Nat} (h : ldh c = true) : c ≠ 46 := by
  simp [ldh] at h; omega

/-- A matched host has no NUL byte anywhere (the `paypal.com\0.evil.com` trick of 2009 cannot match). -/
theorem names_no_nul {pat host : List Nat} (h : nameMatches pat host = true) : 0 ∉ host := by
  simp only [nameMatches, Bool.and_eq_true, hostOk, List.all_eq_true] at h
  obtain ⟨⟨_, hall⟩, _⟩ := h
  intro h0
  have hmem : (0 : Nat) ∈ host.map lower := List.mem_map.mpr ⟨0, h0, by simp [lower]⟩
  rw [← join_split (host.map lower)] at hmem
  have : ∃ l ∈ split (host.map lower), (0 : Nat) ∈ l := by
    generalize split (host.map lower) = ls at hmem ⊢
    induction ls with
    | nil => simp [join] at hmem
    | cons l ls ih =>
      cases ls with
      | nil => exact ⟨l, by simp, by simpa [join] using hmem⟩
      | cons l' ls' =>
        simp only [join, List.mem_append, List.mem_cons] at hmem
        rcases hmem with hm | hm | hm
        · exact ⟨l, by simp, hm⟩
        · omega
        · obtain ⟨l'', hl'', h''⟩ := ih (by simpa [join] using hm)
          exact ⟨l'', List.mem_cons_of_mem _ hl'', h''⟩
  obtain ⟨l, hl, h0l⟩ := this
  have := hall l hl
  simp only [labelOk, Bool.and_eq_true, List.all_eq_true] at this
  exact ldh_ne_zero (this.2 0 h0l) rfl

/-- A wildcard stands for exactly one whole label: the host is one non-empty label with no dot in it,
then a dot, then exactly the rest of the pattern (ignoring case), which has at least two labels. -/
theorem wildcard_one_label {rest : List (List Nat)} {pat host : List Nat}
    (hp : split (pat.map lower) = [42] :: rest) (h : nameMatches pat host = true) :
    2 ≤ rest.length ∧
    ∃ l, l ≠ [] ∧ 46 ∉ l ∧ host.map lower = l ++ 46 :: join rest := by
  simp only [nameMatches, hp, hostOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hlen, hall⟩, ⟨⟨h2, _⟩, htail⟩⟩ := h
  refine ⟨h2, ?_⟩
  have hsplit := join_split (host.map lower)
  cases hs : split (host.map lower) with
  | nil => exact absurd hs (split_ne_nil _)
  | cons l ls =>
    rw [hs] at htail hall hsplit hlen
    simp only [List.tail_cons] at htail; subst htail
    have hl := hall
    simp only [List.all_cons, labelOk, Bool.and_eq_true, decide_eq_true_eq] at hl
    refine ⟨l, by simpa using hl.1.1.1, split_no_dot _ l (by rw [hs]; simp), ?_⟩
    rw [← hsplit]
    cases ls with
    | nil => simp at h2
    | cons r rs => rfl

/-- The pattern `*.com` names no host at all. -/
theorem star_dot_com (host : List Nat) : nameMatches (Sha256.ascii "*.com") host = false := by
  have : split ((Sha256.ascii "*.com").map lower) = [[42], [99, 111, 109]] := by decide +kernel
  simp [nameMatches, this]

/-- Without a wildcard, a match is equality, ignoring case. -/
theorem exact_match {pat host : List Nat} (hp : ∀ rest, split (pat.map lower) ≠ [42] :: rest)
    (h : nameMatches pat host = true) : pat.map lower = host.map lower := by
  simp only [nameMatches, Bool.and_eq_true] at h
  obtain ⟨_, h⟩ := h
  have h' : split (pat.map lower) = split (host.map lower) := by simpa using h
  rw [← join_split (pat.map lower), h', join_split]

end X509.Host
