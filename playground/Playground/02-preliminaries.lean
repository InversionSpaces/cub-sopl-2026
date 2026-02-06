import Mathlib.Tactic.Basic

universe u

abbrev S := Type u

def ref_closure (R R' : S → S → Prop) : Prop :=
  (∀ x, R' x x) ∧ ∀ x y, R x y → R' x y

def trans_closure (R R' : S → S → Prop) : Prop :=
  (∀ x y z, R' x y ∧ R' y z → R' x z) ∧ ∀ x y, R x y → R' x y

def ref_trans_closure (R R' : S → S → Prop) : Prop :=
  ref_closure R R' ∧ trans_closure R R'

section ex2_2_6

example (R : S → S → Prop) :
  let R' := fun x y => R x y ∨ x = y
  ref_closure R R' := by
  unfold ref_closure
  intro R'
  constructor
  { simp [R'] }
  intro x y hR
  simp [R', hR]

end ex2_2_6

section ex2_2_7

def R_i (R : S → S → Prop) (i : Nat) : S → S → Prop :=
  match i with
  | .zero => R
  | .succ n =>
    fun s u =>
      R_i R n s u ∨ ∃ t, R_i R n s t ∧ R_i R n t u

theorem R_i_contains (R : S → S → Prop) (n m : Nat) :
  n ≤ m → ∀ x y, R_i R n x y → R_i R m x y := by
  induction m generalizing n <;> grind [R_i]

def R_trans (R : S → S → Prop) : S → S → Prop :=
  fun x y => ∃ i, R_i R i x y

example (R : S → S → Prop) :
  trans_closure R (R_trans R) := by
  unfold trans_closure R_trans
  constructor
  { intro x y z hRxy
    rcases hRxy with ⟨⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩
    exists max n₁ n₂ + 1
    unfold R_i
    apply Or.inr
    exists y
    constructor
    { apply R_i_contains R n₁ (max n₁ n₂) <;> grind }
    apply R_i_contains R n₂ (max n₁ n₂) <;> grind }
  intro x y hR
  exists 0

end ex2_2_7

section ex2_2_8

def preserved_pred (P : S → Prop) (R : S → S → Prop) : Prop :=
  ∀ s s', R s s' ∧ P s → P s'

example (P : S → Prop) (R : S → S → Prop) :
  preserved_pred P R → preserved_pred P (R_trans R) := by
  unfold preserved_pred
  intro hR s s' hP
  unfold R_trans at hP
  rcases hP with ⟨⟨n, hn⟩, hs⟩
  induction n generalizing s s'
  { simp [R_i] at hn
    grind }
  grind [R_i]

end ex2_2_8


section ax2_4_2

lemma bounded_version (P : Nat → Prop) : ∀ k, (∀ n, (∀ m < n, P m) → P n) → ∀ n < k, P n := by
  intro k
  induction k <;> grind

example (P : Nat → Prop) : (∀ n, (∀ m < n, P m) → P n) → ∀ n, P n := by
  intro hgen n
  have bounded := bounded_version P (n + 1)
  grind

end ax2_4_2

#check WellFounded.induction
