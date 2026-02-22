import Mathlib.Tactic.Basic

import tapl.s05lambdaCalculus

namespace Nameless

open LambdaCalculus

abbrev STerm := LambdaCalculus.Term String

-- De Brujin Level Terms
inductive BLTerm
| Var (x : ℕ) : BLTerm
| Abs (t : BLTerm) : BLTerm
| App (t1 : BLTerm) (t2 : BLTerm) : BLTerm

inductive BLTerm.FVn : ℕ → BLTerm → Prop
| var : x < n → FVn n (.Var x)
| abs : FVn (n + 1) t → FVn n (.Abs t)
| app : FVn n t1 → FVn n t2 → FVn n (.App t1 t2)

def NameCtx := List String

def remove_names (ctx : NameCtx) (t : STerm) : BLTerm :=
  match t with
  | .Var s => .Var (ctx.idxOf s)
  | .Abs n t => .Abs (remove_names (n :: ctx) t)
  | .App t1 t2 => .App (remove_names ctx t1) (remove_names ctx t2)

lemma remove_names_fv {ctx : NameCtx} {t : STerm}
  (h : ∀ s ∈ FV t, ctx.contains s) :
  (remove_names ctx t).FVn ctx.length := by
  induction t generalizing ctx
  · constructor
    simp only [FV, Finset.mem_singleton] at h
    grind
  · rename_i x _ ih
    constructor
    apply ih (ctx := x :: ctx)
    intro s
    by_cases s = x
    · grind
    · grind [FV]
  · rename_i ih1 ih2
    simp only [remove_names]
    constructor
    · apply ih1
      grind [FV]
    · apply ih2
      grind [FV]

namespace Semantics

def shift_up_from (c : ℕ) : BLTerm → BLTerm
| .Var x => if x < c then .Var x else .Var (x.succ)
| .Abs t => .Abs (shift_up_from (c + 1) t)
| .App t1 t2 => .App (shift_up_from c t1) (shift_up_from c t2)

def shift_up (s : BLTerm) : BLTerm := shift_up_from 0 s

def shift_down_from (c : ℕ) : BLTerm → BLTerm
| .Var x => if x < c then .Var x else .Var (x.pred)
| .Abs t => .Abs (shift_down_from (c + 1) t)
| .App t1 t2 => .App (shift_down_from c t1) (shift_down_from c t2)

def shift_down (s : BLTerm) : BLTerm := shift_down_from 0 s

def substN (j : ℕ) (s : BLTerm) : BLTerm → BLTerm
| .Var x => if x = j then s else .Var x
| .Abs t => .Abs (substN (j + 1) (shift_up s) t)
| .App t1 t2 => .App (substN j s t1) (substN j s t2)

def subst (s t : BLTerm) : BLTerm := substN 0 s t

namespace CallByName

inductive Value : BLTerm → Prop
| var : Value (.Var x)
| abs : Value (.Abs t)

inductive SmallStep : BLTerm → BLTerm → Prop
| appL : SmallStep t1 t1' → SmallStep (.App t1 t2) (.App t1' t2)
| beta : SmallStep (.App (.Abs t1) t2) (subst t2 t1)

def MultiStep : BLTerm → BLTerm → Prop := Relation.ReflTransGen SmallStep

theorem determinism
  (h1 : SmallStep t t1)
  (h2 : SmallStep t t2) : t1 = t2 := by
  induction t generalizing t1 t2
  · contradiction
  · contradiction
  · cases h1 <;> cases h2
    · grind
    · contradiction
    · contradiction
    · grind

end CallByName

namespace CallByValue

inductive Value : BLTerm → Prop
| var : Value (.Var x)
| abs : Value (.Abs t)

inductive SmallStep : BLTerm → BLTerm → Prop
| appL : SmallStep t1 t1' → SmallStep (.App t1 t2) (.App t1' t2)
| appR : Value t1 → SmallStep t2 t2' → SmallStep (.App t1 t2) (.App t1 t2')
| beta : Value t2 → SmallStep (.App (.Abs t1) t2) (subst t2 t1)

def MultiStep : BLTerm → BLTerm → Prop := Relation.ReflTransGen SmallStep

end CallByValue

infix:50 " ~cbn~> " => CallByName.MultiStep
infix:50 " ~cbv~> " => CallByValue.MultiStep

abbrev CBNameV := CallByName.Value
abbrev CBValueV := CallByValue.Value

def CBNameNormalizable (t : BLTerm) : Prop := ∃ t', t ~cbn~> t' ∧ CBNameV t'
def CBValueNormalizable (t : BLTerm) : Prop := ∃ t', t ~cbv~> t' ∧ CBValueV t'

lemma value_form_subst_value (s t : BLTerm) :
  CBValueV (subst s t) → CBValueV t := by
  intro h
  cases t
  · simp only [subst, substN] at h
    split_ifs at h
    repeat constructor
  · simp only [subst, substN] at h
    constructor
  · contradiction

lemma cbv_norm_app (h : CBValueNormalizable (t1.App t2)) :
  CBValueNormalizable t1 ∧ CBValueNormalizable t2 := by
  obtain ⟨t', hsteps, hval⟩ := h
  generalize heq : t1.App t2 = t at hsteps
  induction hsteps
    using Relation.ReflTransGen.head_induction_on
    generalizing t1 t2
  · rw [← heq] at hval
    contradiction
  · rename_i hstep steps ih
    rw [← heq] at hstep
    cases hstep
    · rename_i t1' hstep1
      have ⟨ hn1, hn2 ⟩ := ih rfl
      constructor
      · have ⟨ v1' , hsteps', hval' ⟩ := hn1
        use v1'
        constructor
        · apply Relation.ReflTransGen.head
          · assumption
          · assumption
        · assumption
      · assumption
    · rename_i t2' hstep2
      have ⟨ hn1, hn2 ⟩ := ih rfl
      constructor
      · assumption
      · have ⟨ v2' , hsteps', hval' ⟩ := hn2
        use v2'
        constructor
        · apply Relation.ReflTransGen.head
          · assumption
          · assumption
        · assumption
    · rename_i t1 _
      constructor
      · use t1.Abs
        repeat constructor
      · use t2
        repeat constructor
        assumption

theorem cbv_implies_cbn (h : CBValueNormalizable t) : CBNameNormalizable t := by
  induction t
  · repeat constructor
  · rename_i body _
    use body.Abs
    repeat constructor
  · rename_i tl tr ihl ihr
    have ⟨ n , hcb, hcbv ⟩ := h
    cases hcb
    · contradiction
    · sorry

def beta_red (k : ℕ) (t s : BLTerm) := shift_down_from k (subst k (shift_up_from k s) t)

inductive Step : BLTerm → BLTerm → Prop
| refl : Step t t
| abs : Step t t' → Step (.Abs t) (.Abs t')
| app : Step t t' → Step s s' → Step (.App t s) (.App t' s')
| beta : Step t t' → Step s s' → Step (.App (.Abs t) s) (beta_red 0 t' s')

theorem shift_up_down (t : BLTerm) :
  shift_down_from x (shift_up_from x t) = t := by
    unhygienic induction t generalizing x
    { rw [shift_up_from]
      split_ifs with h
      { rw [shift_down_from, if_pos h] }
      rw [shift_down_from, if_neg]
      { rfl }
      omega }
    { rw [shift_up_from, shift_down_from]
      grind }
    rw [shift_up_from, shift_down_from]
    grind

lemma beta_dist (t1 t2 s : BLTerm) :
  beta_red k (t1.App t2) s = (beta_red k t1 s).App (beta_red k t2 s) := by
    rw [beta_red, beta_red, subst, shift_down_from]
    rfl

--probably correct and needs a generalization
lemma beta_some_lemma (t s : BLTerm) :
  n = 0 → (beta_red n (shift_up_from (k + 1) t) (shift_up_from k s)) =
  shift_up_from k (beta_red n t s) := by
    unhygienic induction t generalizing n k
    { repeat rw [beta_red]
      grind [Nat.pred_eq_sub_one, shift_down_from, shift_up_from, shift_up_down, subst] }
    { simp [beta_red, subst, shift_down_from, shift_up_from]
      intro heq
      have := t_ih (n := n + 1) (k := k + 1) sorry
      simp [beta_red] at this
      sorry }
    rw [beta_dist, shift_up_from, shift_up_from, beta_dist]
    grind

lemma beta_shift (t t' : BLTerm) :
  Step t t' → Step (shift_up_from k t) (shift_up_from k t') := by
    intro ht
    unhygienic induction ht generalizing k
    { apply Step.refl }
    { repeat rw [shift_up_from]
      apply Step.abs
      grind }
    { repeat rw [shift_up_from]
      apply Step.app <;> grind }
    repeat rw [shift_up_from]
    have h1 := a_ih (k := k + 1)
    have h2 := a_ih_1 (k := k)
    have := Step.beta h1 h2
    rw [beta_some_lemma] at this
    { apply this }
    omega

-- should be correct
theorem step_beta (s t s' t' : BLTerm) :
  Step s s' → Step t t' → Step (beta_red 0 t s) (beta_red 0 t' s') := by
    intro hs ht
    unhygienic induction t generalizing t' s s'
    { cases ht
      rw [beta_red, subst, beta_red, subst]
      split_ifs with h
      { rw [shift_up_down, shift_up_down]
        exact hs }
      apply Step.refl }
    { --simp only [beta_red, subst, zero_add, shift_down_from]
      unhygienic cases ht
      { apply Step.abs
        sorry }
      apply Step.abs
      sorry }
    unhygienic cases ht
    { rw [beta_dist, beta_dist]
      apply Step.app
      { apply t1_ih s s' t1 hs (by grind [Step]) }
      apply t2_ih s s' t2 hs (by grind [Step]) }
    { rw [beta_dist, beta_dist]
      apply Step.app
      { apply t1_ih s s' t'_1 hs a }
      apply t2_ih s s' s'_1 hs a_1 }
    rw [beta_dist]
    sorry

theorem step_inj (s t1 t2 : BLTerm) :
  Step s t1 → Step s t2 → ∃ r, Step t1 r ∧ Step t2 r := by
    unhygienic induction s generalizing t1 t2
    { grind [Step] }
    { intro h1 h2
      unhygienic cases h1
      { exists t2
        grind [Step] }
      unhygienic cases h2
      { exists t'.Abs
        grind [Step] }
      rcases t_ih t' t'_1 a a_1 with ⟨r, hr⟩
      exists .Abs r
      grind [Step] }
    intro h1 h2
    unhygienic cases h1 <;> unhygienic cases h2
    { exists t1.App t2
      grind [Step] }
    { exists t'.App s'
      grind [Step] }
    { exists beta_red 0 t' s'
      grind [Step] }
    { exists t'.App s'
      grind [Step] }
    { rcases t1_ih t' t'_1 a a_2 with ⟨t2, ht2⟩
      rcases t2_ih s' s'_1 a_1 a_3 with ⟨s2, hs2⟩
      exists t2.App s2
      grind [Step] }
    { rcases t2_ih s' s'_1 a_1 a_3 with ⟨s2, hs2⟩
      unhygienic cases a
      { exists beta_red 0 t'_1 s2
        constructor
        { apply Step.beta a_2 hs2.1 }
        apply step_beta _ _ _ _ hs2.2
        apply Step.refl }
      rcases t1_ih t'_1.Abs t'_2.Abs (by grind [Step]) (by grind [Step]) with ⟨t2, ht2⟩
      unhygienic cases t2
      { grind [Step] }
      { exists beta_red 0 t_1 s2
        constructor
        { apply Step.beta (by grind [Step]) hs2.1 }
        apply step_beta _ _ _ _ hs2.2
        grind [Step] }
      grind [Step] }
    { exists beta_red 0 t' s'
      grind [Step] }
    { rcases t2_ih s' s'_1 a_1 a_3 with ⟨s2, hs2⟩
      unhygienic cases a_2
      { exists beta_red 0 t' s2
        constructor
        { apply step_beta _ _ _ _ hs2.1
          apply Step.refl    }
        apply Step.beta a hs2.2 }
      rcases t1_ih t'.Abs t'_2.Abs (by grind [Step]) (by grind [Step]) with ⟨t2, ht2⟩
      unhygienic cases t2
      { grind [Step] }
      { exists beta_red 0 t_1 s2
        constructor
        { apply step_beta _ _ _ _ hs2.1
          grind [Step] }
        apply Step.beta (by grind [Step]) hs2.2 }
      grind [Step] }
    rcases t1_ih t'.Abs t'_1.Abs (by grind [Step]) (by grind [Step]) with ⟨r1, hr1⟩
    rcases t2_ih _ _ a_1 a_3 with ⟨r2, hr2⟩
    unhygienic cases r1
    { grind [Step] }
    { exists beta_red 0 t_1 r2
      constructor
      { apply step_beta _ _ _ _ hr2.1
        grind [Step] }
      apply step_beta _ _ _ _ hr2.2
      grind [Step] }
    grind [Step]

end Semantics

end Nameless
