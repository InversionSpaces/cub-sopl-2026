import Mathlib.Tactic.Basic

namespace Untyped

namespace Section3

inductive Lang
| zero
| True
| False
| succ (exp : Lang)
| pred (exp : Lang)
| iszero (exp : Lang)
| If (cond exp₁ exp₂ : Lang)

def size : Lang → Nat
| .zero => 1
| .True => 1
| .False => 1
| .succ exp => 1 + size exp
| .pred exp => 1 + size exp
| .iszero exp => 1 + size exp
| .If cond exp₁ exp₂ => 1 + size cond + size exp₁ + size exp₂


def depth : Lang → Nat
| .zero => 1
| .True => 1
| .False => 1
| .succ exp => 1 + depth exp
| .pred exp => 1 + depth exp
| .iszero exp => 1 + depth exp
| .If cond exp₁ exp₂ => 1 + max (max (depth cond) (depth exp₁)) (depth exp₂)

lemma induction_size_specified (P : Lang → Prop) :
  ∀ gen_sz, (∀ (s : Lang), (∀ r, size r < size s → P r) → P s) → ∀ s, size s < gen_sz  → P s := by
    intro gen_sz ind s hlt
    induction gen_sz generalizing s
    { simp [*] at hlt }
    rename_i n hn
    by_cases size s = n
    { grind }
    grind

theorem induction_size (P : Lang → Prop) :
  (∀ (s : Lang), (∀ r, size r < size s → P r) → P s) → ∀ s, P s := by
    intro ind s
    exact induction_size_specified P (size s + 1) ind s (by simp)

lemma induction_depth_specified (P : Lang → Prop) :
  ∀ gen_sz, (∀ (s : Lang), (∀ r, depth r < depth s → P r) → P s) →
  ∀ s, depth s < gen_sz  → P s := by
    intro gen_sz ind s hlt
    induction gen_sz generalizing s
    { simp [*] at hlt }
    rename_i n hn
    by_cases depth s = n
    { grind }
    grind

theorem induction_depth (P : Lang → Prop) :
  (∀ (s : Lang), (∀ r, depth r < depth s → P r) → P s) → ∀ s, P s := by
    intro ind s
    exact induction_depth_specified P (depth s + 1) ind s (by simp)

#check Lang.recOn

end Section3

namespace Booleans

inductive Term : Type
| True : Term
| False : Term
| If (c t e : Term) : Term

inductive Value : Term → Prop
| TrueV : Value Term.True
| FalseV : Value Term.False

inductive Step : Term → Term → Prop
| IfTrue : Step (Term.If Term.True t e) t
| IfFalse : Step (Term.If Term.False t e) e
| IfStep : Step c c' → Step (Term.If c t e) (Term.If c' t e)

theorem determinism : Step t t₁ → Step t t₂ → t₁ = t₂ := by
  intro s1 s2
  induction s1 generalizing t₂ <;> cases s2
  all_goals (
    try contradiction
    try grind
  )

def Normal : Term → Prop
| t => ¬ ∃ t', Step t t'

theorem value_is_normal : Value v → Normal v := by
  intro hv
  cases hv <;> intro ⟨ t', hstep ⟩ <;> cases hstep

theorem normal_is_value : Normal v → Value v := by
  intro hn
  induction v <;> repeat constructor
  rename_i c t e c_ih t_ih e_ih
  cases c
  · cases hn ⟨ _, Step.IfTrue ⟩
  · cases hn ⟨ _, Step.IfFalse ⟩
  · cases c_ih (by
      intro ⟨ c', hstep ⟩
      apply hn
      exact ⟨ _, Step.IfStep hstep ⟩
    )

inductive MultiStep : Term → Term → Prop
| Refl : MultiStep t t
| Step : Step t t' → MultiStep t' t'' → MultiStep t t''

lemma multi_step_multi_step : MultiStep t t' → MultiStep t' t'' → MultiStep t t'' := by
  intro ms1 ms2
  induction ms1
  · assumption
  · rename_i ih
    apply MultiStep.Step
    · assumption
    · apply ih
      assumption

lemma multi_if_step : MultiStep c c' →
  MultiStep (Term.If c t e) (Term.If c' t e) := by
  intro ms
  induction ms
  · apply MultiStep.Refl
  · apply MultiStep.Step
    · apply Step.IfStep
      assumption
    · assumption

theorem unique_normal_form :
  MultiStep t v₁ → MultiStep t v₂ → Normal v₁ → Normal v₂ → v₁ = v₂ := by
  intro ms1 ms2 hn1 hn2
  induction ms1 generalizing v₂ <;> cases ms2
  · rfl
  · cases hn1 ⟨ _, by assumption ⟩
  · cases hn2 ⟨ _, by assumption ⟩
  · rename_i s2 _ ih t' s1 _
    apply ih
    · rw [determinism s2 s1]
      assumption
    · assumption
    · assumption

theorem termination : ∀ t, ∃ v, MultiStep t v ∧ Normal v := by
  intro t
  induction t
  · exists Term.True
    repeat constructor
    apply value_is_normal
    constructor
  · exists Term.False
    repeat constructor
    apply value_is_normal
    constructor
  · rename_i c t e ihc iht ihe
    have ⟨ vc, hc, hnc ⟩ := ihc
    have ⟨ vt, ht, hnt ⟩ := iht
    have ⟨ ve, he, hne ⟩ := ihe
    cases normal_is_value hnc
    · exists vt
      constructor
      · apply multi_step_multi_step
        · apply multi_if_step hc
        · apply MultiStep.Step
          · exact Step.IfTrue
          · assumption
      · assumption
    · exists ve
      constructor
      · apply multi_step_multi_step
        · apply multi_if_step hc
        · apply MultiStep.Step
          · exact Step.IfFalse
          · assumption
      · assumption

end Booleans

namespace Naturals

inductive Term : Type
| True : Term
| False : Term
| If (c t e : Term) : Term
| Zero : Term
| Succ (t : Term) : Term
| Pred (t : Term) : Term
| IsZero (t : Term) : Term

inductive NatV : Term → Prop
| ZeroV : NatV Term.Zero
| SuccV : NatV t → NatV (Term.Succ t)

inductive Value : Term → Prop
| TrueV : Value Term.True
| FalseV : Value Term.False
| NatV : NatV t → Value t

inductive Step : Term → Term → Prop
| IfTrue : Step (Term.If Term.True t e) t
| IfFalse : Step (Term.If Term.False t e) e
| IfStep : Step c c' → Step (Term.If c t e) (Term.If c' t e)
| SuccStep : Step t t' → Step (Term.Succ t) (Term.Succ t')
| PredZero : Step (Term.Pred Term.Zero) Term.Zero
| PredSucc : NatV t → Step (Term.Pred (Term.Succ t)) t
| PredStep : Step t t' → Step (Term.Pred t) (Term.Pred t')
| IsZeroZero : Step (Term.IsZero Term.Zero) Term.True
| IsZeroSucc : NatV t → Step (Term.IsZero (Term.Succ t)) Term.False
| IsZeroStep : Step t t' → Step (Term.IsZero t) (Term.IsZero t')

inductive MultiStep : Term → Term → Prop
| Refl : MultiStep t t
| Step : Step t t' → MultiStep t' t'' → MultiStep t t''

lemma nv_no_step : NatV t → ¬ Step t t' := by
  induction t generalizing t'
  all_goals (
    intro hnv
    cases hnv
    try contradiction
  )
  · intro s
    cases s
  · intro s
    cases s
    grind

theorem determinism : Step t t₁ → Step t t₂ → t₁ = t₂ := by
  intro s1 s2
  induction s1 generalizing t₂ <;> cases s2
  all_goals (
    try contradiction
    try grind
  )
  · rename_i s
    cases s
    cases nv_no_step (by assumption) (by assumption)
  · rename_i s ih
    cases s
    cases nv_no_step (by assumption) (by assumption)
  · rename_i s
    cases s
    cases nv_no_step (by assumption) (by assumption)
  · rename_i s ih
    cases s
    cases nv_no_step (by assumption) (by assumption)

def Normal : Term → Prop
| t => ¬ ∃ t', Step t t'

lemma nv_is_normal : NatV t → Normal t := by
  intro hnv
  induction t <;> cases hnv
              <;> intro ⟨ t', hstep ⟩
              <;> cases hstep
  rename_i ih hnv t' s
  exact ih hnv ⟨ t', s ⟩

theorem value_is_normal : Value v → Normal v := by
  intro hv
  cases hv <;> intro ⟨ t', hstep⟩
  · cases hstep
  · cases hstep
  · apply nv_is_normal (by assumption) ⟨ t', hstep ⟩

def Stuck : Term → Prop
| t => Normal t ∧ ¬ Value t

inductive BigStep : Term → Term → Prop
| Value : Value v → BigStep v v
-- Do we need Value v in those two cases below?
| IfTrue : Value v → BigStep c Term.True → BigStep t v → BigStep (Term.If c t e) v
| IfFalse : Value v → BigStep c Term.False → BigStep e v → BigStep (Term.If c t e) v
| Succ : NatV v → BigStep t v → BigStep (Term.Succ t) (Term.Succ v)
| PredZero : BigStep t Term.Zero → BigStep (Term.Pred t) Term.Zero
| PredSucc : NatV v → BigStep t (Term.Succ v) → BigStep (Term.Pred t) v
| IsZeroZero : BigStep t Term.Zero → BigStep (Term.IsZero t) Term.True
| IsZeroSucc : NatV v → BigStep t (Term.Succ v) → BigStep (Term.IsZero t) Term.False

theorem big_step_is_multi_step : BigStep t v ↔ MultiStep t v := by
  constructor
  · sorry
  · sorry

end Naturals

end Untyped
