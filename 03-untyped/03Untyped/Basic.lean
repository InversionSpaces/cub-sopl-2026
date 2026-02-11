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
    --improve grind
    grind [Step, NatV]
  )

theorem determinism : Step t t₁ → Step t t₂ → t₁ = t₂ := by
  intro s1 s2
  induction s1 generalizing t₂ <;> cases s2
  all_goals (
    --improve grind
    try grind [nv_no_step, Step]
  )

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

theorem aug_multi_step : ∀ f : Term → Term,
  (∀ t t', (Step t t' → Step (f t) (f t'))) →
  MultiStep t t' → MultiStep (f t) (f t') := by
  intro f hf ht
  induction ht <;> grind [MultiStep]

theorem multi_step_trans : MultiStep t t' → MultiStep t' t'' → MultiStep t t'' := by
  intro h
  induction h <;> grind [MultiStep]

inductive WTerm
| True : WTerm
| False : WTerm
| If (c t e : WTerm) : WTerm
| Zero : WTerm
| Succ (t : WTerm) : WTerm
| Pred (t : WTerm) : WTerm
| IsZero (t : WTerm) : WTerm
| Wrong

def Eqt : WTerm → Term → Prop
| .True, .True => True
| .False, .False => True
| .If c₁ t₁ e₁, .If c t e => Eqt c₁ c ∧ Eqt t₁ t ∧ Eqt e₁ e
| .Zero, .Zero => True
| .Succ t₁, .Succ t₂ => Eqt t₁ t₂
| .Pred t₁, .Pred t₂ => Eqt t₁ t₂
| .IsZero t₁, .IsZero t₂ => Eqt t₁ t₂
| .Wrong, _ => False
| _, _ => False

inductive BadNat : WTerm → Prop
| BadTrue : BadNat (.True)
| BadFalse : BadNat (.False)
| BadWrong : BadNat (.Wrong)

inductive BadBool : WTerm → Prop
| BadSucc : BadBool (.Succ v)
| BadZero : BadBool (.Zero)
| BadWrong : BadBool (.Wrong)

inductive WStep : WTerm → WTerm → Prop
| IfTrue : WStep (.If .True t e) t
| IfFalse : WStep (.If .False t e) e
| IfStep : WStep c c' → WStep (.If c t e) (.If c' t e)
| SuccStep : WStep t t' → WStep (.Succ t) (.Succ t')
| PredZero : WStep (.Pred .Zero) .Zero
| PredSucc : Eqt t₁ t₂ → NatV t₂ → WStep (.Pred (.Succ t₁)) t₁
| PredStep : WStep t t' → WStep (.Pred t) (.Pred t')
| IsZeroZero : WStep (.IsZero .Zero) .True
| IsZeroSucc : Eqt t₁ t₂ → NatV t₂ → WStep (.IsZero (.Succ t₁)) .False
| IsZeroStep : WStep t t' → WStep (.IsZero t) (.IsZero t')
| IfBadBool : BadBool t → WStep (.If t p n) .Wrong
| SuccWrong : BadNat t → WStep (.Succ t) .Wrong
| PredWrong : BadNat t → WStep (.Pred t) .Wrong
| IsZeroWrong : BadNat t → WStep (.IsZero t) .Wrong


inductive WMultiStep : WTerm → WTerm → Prop
| Refl : WMultiStep t t
| Step : WStep t t' → WMultiStep t' t'' → WMultiStep t t''


def WNormal : WTerm → Prop
| t => ¬ ∃ t', WStep t t'

theorem stuck_if : Stuck (Term.If t p n) → (Stuck t ∨ NatV t) := by
  unfold Stuck Normal
  simp only [not_exists, and_imp]
  intro hx hv
  by_cases hnv : NatV t
  { simp [hnv] }
  simp only [hnv, or_false]
  constructor
  { intro x stx
    have := Step.IfStep stx (t := p) (e := n)
    grind [Step] }
  intro hvt
  cases hvt
  { have := Step.IfTrue (t := p) (e := n)
    grind }
  { have := Step.IfFalse (t := p) (e := n)
    grind }
  grind [Stuck, Normal, Value, Step]

theorem stuck_succ : Stuck (Term.Succ t) → (Stuck t ∨ t = .False ∨ t = .True) := by
  unfold Stuck Normal
  simp only [not_exists, and_imp]
  intro hx hv
  by_cases hnv : t = Term.False ∨ t = Term.True
  { simp [hnv] }
  simp only [hnv, or_false]
  constructor
  { intro x stx
    have := Step.SuccStep stx
    grind [Step] }
  grind [Stuck, Normal, Value, Step, NatV]

theorem stuck_pred : Stuck (Term.Pred t) → (Stuck t ∨ t = .False ∨ t = .True) := by
  unfold Stuck Normal
  simp only [not_exists, and_imp]
  intro hx hv
  by_cases hnv : t = Term.False ∨ t = Term.True
  { simp [hnv] }
  simp only [hnv, or_false]
  constructor
  { intro x stx
    have := Step.PredStep stx
    grind [Step] }
  intro hvt
  cases hvt
  { grind }
  { grind }
  rename_i hvs
  unhygienic cases hvs
  { grind [Value, Step] }
  have := Step.PredSucc a
  grind [Stuck, Normal, Value, Step, NatV]

theorem stuck_isZero : Stuck (Term.IsZero t) → (Stuck t ∨ t = .False ∨ t = .True) := by
  unfold Stuck Normal
  simp only [not_exists, and_imp]
  intro hx hv
  by_cases hnv : t = Term.False ∨ t = Term.True
  { simp [hnv] }
  simp only [hnv, or_false]
  constructor
  { intro x stx
    have := Step.IsZeroStep stx
    grind [Step] }
  intro hvt
  unhygienic cases hvt
  { grind }
  { grind }
  unhygienic cases a
  { grind [Step] }
  have := Step.IsZeroSucc a_1
  grind [Stuck, Normal, Value, Step, NatV]


theorem aug_wmulti_step (t₁ t₂ : WTerm) : ∀ f : WTerm → WTerm,
  (∀ t t', (WStep t t' → WStep (f t) (f t'))) →
  WMultiStep t₁ t₂ → WMultiStep (f t₁) (f t₂) := by
  intro f hf ht
  induction ht <;> grind [WMultiStep]

theorem multi_wstep_trans : WMultiStep t t' → WMultiStep t' t'' → WMultiStep t t'' := by
  intro h
  induction h <;> grind [WMultiStep]

theorem stuck_is_wrong : Eqt t₁ t → Stuck t → WMultiStep t₁ .Wrong := by
  intro eq st
  unhygienic fun_induction Eqt
  { grind [Stuck, Normal, Value, Step, WStep] }
  { grind [Stuck, Normal, Value, Step, WStep] }
  { unhygienic cases stuck_if st
    { apply multi_wstep_trans
      { apply aug_wmulti_step c₁ .Wrong (fun t₁ => t₁.If t₁_1 e₁) (by grind [WStep]) (by grind) }
      apply WMultiStep.Step
      { apply WStep.IfBadBool
        grind [BadBool] }
      grind [WMultiStep] }
    have : BadBool c₁ := by
      cases h
      { have : c₁ = WTerm.Zero := by grind [Eqt]
        grind [BadBool] }
      { have : ∃ t1, c₁ = WTerm.Succ t1 := by
          have str := eq.1
          unfold Eqt at str
          split at str
          all_goals try grind
        grind [BadBool] }
    apply WMultiStep.Step
    { apply WStep.IfBadBool
      grind [BadBool] }
    grind [WMultiStep] }
  { grind [Stuck, Normal, Value, NatV] }
  { unhygienic cases stuck_succ st
    { apply multi_wstep_trans
      { apply aug_wmulti_step t₁_1 .Wrong .Succ (by grind [WStep]) (by grind) }
      apply WMultiStep.Step
      { apply WStep.SuccWrong
        grind [BadNat] }
      grind [WMultiStep] }
    cases h <;>
    { have : t₁_1 = WTerm.False ∨ t₁_1 = WTerm.True := by grind [Eqt]
      apply WMultiStep.Step
      { apply WStep.SuccWrong
        grind [WMultiStep, WStep, BadNat, Eqt] }
      apply WMultiStep.Refl } }
  { unhygienic cases stuck_pred st
    { apply multi_wstep_trans
      { apply aug_wmulti_step t₁_1 .Wrong .Pred (by grind [WStep]) (by grind) }
      apply WMultiStep.Step
      { apply WStep.PredWrong
        grind [BadNat] }
      grind [WMultiStep] }
    cases h <;>
    { have : t₁_1 = WTerm.False ∨ t₁_1 = WTerm.True := by grind [Eqt]
      apply WMultiStep.Step
      { apply WStep.PredWrong
        grind [WMultiStep, WStep, BadNat, Eqt] }
      apply WMultiStep.Refl } }
  { unhygienic cases stuck_isZero st
    { apply multi_wstep_trans
      { apply aug_wmulti_step t₁_1 .Wrong .IsZero (by grind [WStep]) (by grind) }
      apply WMultiStep.Step
      { apply WStep.IsZeroWrong
        grind [BadNat] }
      grind [WMultiStep] }
    cases h <;>
    { have : t₁_1 = WTerm.False ∨ t₁_1 = WTerm.True := by grind [Eqt]
      apply WMultiStep.Step
      { apply WStep.IsZeroWrong
        grind [WMultiStep, WStep, BadNat, Eqt] }
      apply WMultiStep.Refl } }
  { apply WMultiStep.Refl }
  grind

theorem step_is_wstep : Eqt t₁ t1 → (Step t1 t2) → ∃ t₂, (WStep t₁ t₂) ∧ Eqt t₂ t2 := by
  intro eq st
  unhygienic fun_induction Eqt generalizing t2
  { exists WTerm.True }
  { exists WTerm.False }
  { unhygienic cases st
    { have : c₁ = WTerm.True := by grind [Eqt]
      exists t₁_1
      grind [WStep] }
    { have : c₁ = WTerm.False := by grind [Eqt]
      exists e₁
      grind [WStep] }
    rcases ih3 (t2 := c') eq.1 a with ⟨t2, ht2⟩
    exists t2.If t₁_1 e₁
    grind [WStep, Eqt] }
  { exists WTerm.Zero }
  { unhygienic cases st
    rcases ih1 (t2 := t') eq a with ⟨t₂, ht₂⟩
    exists t₂.Succ
    grind [WStep, Eqt] }
  { unhygienic cases st
    { exists WTerm.Zero
      have : t₁_1 = WTerm.Zero := by grind [Eqt]
      grind [Eqt, WStep] }
    { have : ∃ t₁_2, t₁_1 = WTerm.Succ t₁_2 := by
        unfold Eqt at eq
        split at eq <;> try grind
      rcases this with ⟨tval, htval⟩
      rw [htval]
      exists tval
      grind [WStep, Eqt] }
    rcases ih1 (t2 := t') eq a with ⟨t₂, ht₂⟩
    exists t₂.Pred
    grind [WStep, Eqt] }
  { unhygienic cases st
    { exists WTerm.True
      have : t₁_1 = WTerm.Zero := by grind [Eqt]
      grind [Eqt, WStep] }
    { have : ∃ t₁_2, t₁_1 = WTerm.Succ t₁_2 := by
        unfold Eqt at eq
        split at eq <;> try grind
      rcases this with ⟨tval, htval⟩
      rw [htval]
      exists WTerm.False
      grind [WStep, Eqt] }
    rcases ih1 (t2 := t') eq a with ⟨t₂, ht₂⟩
    exists t₂.IsZero
    grind [WStep, Eqt] }
  { grind }
  grind

theorem eq_det (t1 : WTerm) (t2 t3 : Term) : Eqt t1 t2 → Eqt t1 t3 → t2 = t3 := by
  intro eq
  unhygienic fun_induction Eqt t1 t2 generalizing t3 <;> try grind [Eqt]
  all_goals {
    intro eq1
    unfold Eqt at eq1
    split at eq1 <;> grind }

def size : Term → Nat
| .True => 1
| .False => 1
| .If (c : Term) (t : Term) (e : Term) => 1 + size c + size t + size e
| .Zero => 1
| .Succ (t : Term) => 1 + size t
| .Pred (t : Term) => 1 + size t
| .IsZero (t : Term) => 1 + size t

theorem step_size : Step t t' → size t > size t' := by
  intro h
  unhygienic induction h <;> grind [size]

theorem multi_step_size : MultiStep t t' → size t > size t' ∨ t = t' := by
  intro h
  unhygienic induction h
  { simp }
  cases a_ih <;>
  { have step_sz := step_size a
    grind [step_size] }


def wsize : WTerm → Nat
| .True => 1
| .False => 1
| .If (c : WTerm) (t : WTerm) (e : WTerm) => 1 + wsize c + wsize t + wsize e
| .Zero => 1
| .Succ (t : WTerm) => 1 + wsize t
| .Pred (t : WTerm) => 1 + wsize t
| .IsZero (t : WTerm) => 1 + wsize t
| .Wrong => 1

theorem wstep_size : WStep t t' → wsize t > wsize t' := by
  intro h
  unhygienic induction h <;> try grind [wsize, BadBool, BadNat]

theorem multi_steps_finishes (t : Term) : ∃ t', MultiStep t t' ∧ Normal t' := by
  by_cases ht : Normal t
  { grind [MultiStep] }
  unfold Normal at ht
  have : ∃ t', Step t t' := by grind
  rcases this with ⟨t', ht'⟩
  rcases multi_steps_finishes t' with ⟨t1, ht1⟩
  grind [MultiStep]
termination_by size t
decreasing_by
  apply step_size
  apply ht'

theorem multi_steps_multi_wsteps (t t1 : Term) (t2 : WTerm) :
  Eqt t2 t → MultiStep t t1 → ∃ t3, WMultiStep t2 t3 ∧ Eqt t3 t1 := by
    intro eq hms
    unhygienic cases hms
    { grind [WMultiStep] }
    rcases step_is_wstep eq a with ⟨t3, ht3⟩
    rcases multi_steps_multi_wsteps t' t1 t3 ht3.2 a_1 with ⟨t4, ht4⟩
    exists t4
    simp [ht4]
    grind [WMultiStep]
termination_by size t
decreasing_by
  apply step_size
  grind


theorem wstep_preserves_badbool (t1 t2 : WTerm) :
  WStep t1 t2 → BadBool t1 → BadBool t2 := by
    grind [WStep, BadBool]

theorem wterm_nat (t1 t2 : WTerm) (t : Term) :
  WStep t1 t2 → NatV t → Eqt t1 t → False := by
    intro hs hn heq
    unhygienic cases hn
    { have : t1 = .Zero := by grind [Eqt]
      grind [WStep] }
    have : ∃ t, WTerm.Succ t = t1 := by
      unfold Eqt at heq
      split at heq <;> grind
    rcases this with ⟨t, ht⟩
    unhygienic cases hs <;> try grind
    { apply wterm_nat t_2 t' t_1 a_1 a (by grind [Eqt]) }
    have : Eqt t_2 t_1 := by grind [Eqt]
    unhygienic cases a_1
    { have : t_1 = .True := by grind [Eqt]
      grind [NatV] }
    { have : t_1 = .False := by grind [Eqt]
      grind [NatV] }
    grind [WStep, NatV, Eqt, BadNat]


theorem wstep_det (t1 t2 t3 : WTerm) :
  WStep t1 t2 → WStep t1 t3 →
  t2 = t3 ∨
  WMultiStep t2 .Wrong ∧ WMultiStep t3 .Wrong := by
    intro hs1 hs2
    by_cases t2 = t3
    { apply Or.inl
      assumption }
    apply Or.inr
    unhygienic cases hs1 <;> unhygienic cases hs2 <;> try grind [WStep, BadBool, BadNat]
    { unhygienic cases wstep_det c c' c'_1 a a_1
      { grind }
      constructor <;>
      { apply multi_wstep_trans
        { apply aug_wmulti_step (t₂ := .Wrong) (f := fun t4 => t4.If t e)
          { grind [WStep] }
          grind }
        apply WMultiStep.Step
        { apply WStep.IfBadBool
          grind [WMultiStep, WStep, BadBool] }
        apply WMultiStep.Refl } }
    { constructor
      { have : BadBool c' := by grind [wstep_preserves_badbool]
        apply WMultiStep.Step
        { apply WStep.IfBadBool
          grind [WMultiStep, WStep] }
        apply WMultiStep.Refl }
      apply WMultiStep.Refl }
    { unhygienic cases wstep_det t t' t'_1 a a_1
      { grind }
      constructor <;>
      { apply multi_wstep_trans
        { apply aug_wmulti_step (t₂ := .Wrong) (f := .Succ)
          { grind [WStep] }
          grind }
        apply WMultiStep.Step
        { apply WStep.SuccWrong
          grind [WMultiStep, WStep, BadNat] }
        apply WMultiStep.Refl } }
    { unhygienic cases a_2
      { grind [wterm_nat] }
      cases a_3 <;> grind [Eqt, NatV] }
    { unhygienic cases a
      { grind [wterm_nat] }
      cases a_3 <;> grind [Eqt, NatV] }
    { unhygienic cases wstep_det t t' t'_1 a a_1
      { grind }
      constructor <;>
      { apply multi_wstep_trans
        { apply aug_wmulti_step (t₂ := .Wrong) (f := .Pred)
          { grind [WStep] }
          grind }
        apply WMultiStep.Step
        { apply WStep.PredWrong
          grind [WMultiStep, WStep, BadNat] }
        apply WMultiStep.Refl } }
    { unhygienic cases a_2
      { grind [wterm_nat] }
      cases a_3 <;> grind [Eqt, NatV] }
    { unhygienic cases a
      { grind [wterm_nat] }
      cases a_3 <;> grind [Eqt, NatV] }
    { unhygienic cases wstep_det t t' t'_1 a a_1
      { grind }
      constructor <;>
      { apply multi_wstep_trans
        { apply aug_wmulti_step (t₂ := .Wrong) (f := .IsZero)
          { grind [WStep] }
          grind }
        apply WMultiStep.Step
        { apply WStep.IsZeroWrong
          grind [WMultiStep, WStep, BadNat] }
        apply WMultiStep.Refl } }
    constructor
    { apply WMultiStep.Refl }
    apply WMultiStep.Step
    { apply WStep.IfBadBool
      have : BadBool c' := by grind [wstep_preserves_badbool]
      grind [WMultiStep, WStep] }
    apply WMultiStep.Refl
termination_by wsize t1
decreasing_by
  all_goals grind [wstep_size, wsize]

theorem multi_wstep_wrong (t1 t2 : WTerm) :
  WMultiStep t1 t2 → WMultiStep t1 .Wrong → WMultiStep t2 .Wrong := by
  intro h1 h2
  unhygienic cases h1
  { grind [WMultiStep, WStep] }
  apply multi_wstep_wrong t' t2
  { apply a_1 }
  unhygienic cases h2
  { grind [WMultiStep, WStep] }
  unhygienic cases wstep_det t1 t' t'_1 a a_2
  { grind }
  exact h.1
termination_by wsize t1
decreasing_by
  apply wstep_size
  grind

theorem multi_wstep_natv (t1 t2 : WTerm) (t : Term) :
  WStep t1 t2 → NatV t → Eqt t1 t → False := by
  intro hms eq hn
  unhygienic cases eq
  { have : t1 = .Zero := by grind [Eqt]
    grind [Eqt, WStep] }
  have : ∃ t3, WTerm.Succ t3 = t1 := by
    unfold Eqt at hn
    split at hn <;> grind
  rcases this with ⟨t3, ht3⟩
  have : Eqt t3 t_1 := by grind [Eqt]
  unhygienic cases hms <;> try grind
  { apply multi_wstep_natv t t' t_1 a_1 a (by grind [Eqt]) }
  cases a_1 <;> grind [Eqt, NatV]

theorem stuck_iff_wrong : Eqt t₁ t → (WMultiStep t₁ .Wrong ↔ ∃ t', MultiStep t t' ∧ Stuck t') := by
  intro eq
  constructor
  { intro hwm
    rcases multi_steps_finishes t with ⟨t1, ht1⟩
    exists t1
    simp only [ht1]
    unfold Stuck
    simp only [true_and, ht1]
    intro hv
    rcases multi_steps_multi_wsteps t t1 t₁ eq ht1.1 with ⟨t2, ht2⟩
    have : WMultiStep t2 .Wrong  := by
      apply multi_wstep_wrong t₁ t2 ht2.1 hwm
    unhygienic cases hv
    { have eq : t2 = .True := by grind [Eqt]
      cases this
      { grind }
      grind [WStep] }
    { have eq : t2 = .False := by grind [Eqt]
      cases this
      { grind }
      grind [WStep] }
    cases this
    { grind [Eqt] }
    grind [multi_wstep_natv] }
  rintro ⟨t', ms, st⟩
  unhygienic induction ms generalizing t₁
  { apply stuck_is_wrong eq st }
  rcases step_is_wstep eq a with ⟨t1, ht1⟩
  have lem := a_ih (t₁ := t1) ht1.2 st
  grind [WMultiStep]

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

theorem step_implies_big_step : Value v → Step t t' → BigStep t v → BigStep t' v := by
  intro hv hs hbs
  unhygienic induction t generalizing t' v <;>
  { grind (splits := 20) [BigStep, Value, NatV, Step] }

theorem big_step_implies_step : Value v → Step t' t → BigStep t v → BigStep t' v := by
  intro hv hs hbs
  unhygienic induction t generalizing t' v <;>
  { grind (splits := 20) [BigStep, Value, NatV, Step] }

theorem multi_step_if_eval_true : MultiStep t Term.True → MultiStep ((Term.If t) p n) p := by
  intro hv
  unhygienic cases hv
  { apply MultiStep.Step
    { exact Step.IfTrue }
    { exact MultiStep.Refl } }
  apply MultiStep.Step
  { exact Step.IfStep a }
  apply multi_step_if_eval_true
  exact a_1
termination_by size t
decreasing_by exact step_size a


theorem multi_step_if_eval_false : MultiStep t Term.False → MultiStep ((Term.If t) p n) n := by
  intro hv
  unhygienic cases hv
  { apply MultiStep.Step
    { exact Step.IfFalse }
    { exact MultiStep.Refl } }
  apply MultiStep.Step
  { exact Step.IfStep a }
  apply multi_step_if_eval_false
  exact a_1
termination_by size t
decreasing_by exact step_size a

theorem big_step_is_multi_step : Value v → (BigStep t v ↔ MultiStep t v) := by
  intro hv
  constructor
  { intro hbs
    unhygienic induction hbs
    { grind [MultiStep] }
    { grind [multi_step_if_eval_true, Value, multi_step_trans] }
    { grind [multi_step_if_eval_false, Value, multi_step_trans] }
    { apply aug_multi_step <;> grind [Step, Value] }
    { apply multi_step_trans
      { exact aug_multi_step (f := Term.Pred) (by grind [Step]) (a_ih hv)}
      grind [MultiStep, Step] }
    { have : MultiStep t_1 v_1.Succ := by grind [Value, NatV]
      apply multi_step_trans
      { exact aug_multi_step (f := Term.Pred) (by grind [Step]) this }
      apply MultiStep.Step
      { exact Step.PredSucc a }
      grind [MultiStep, Step] }
    { have : MultiStep t_1 Term.Zero := by grind [Value, NatV]
      apply multi_step_trans
      { exact aug_multi_step (f := Term.IsZero) (by grind [Step]) this }
      apply MultiStep.Step
      { exact Step.IsZeroZero }
      grind [MultiStep, Step] }
    have : MultiStep t_1 v_1.Succ := by grind [Value, NatV]
    apply multi_step_trans
    { exact aug_multi_step (f := Term.IsZero) (by grind [Step]) this }
    apply MultiStep.Step
    { exact Step.IsZeroSucc a }
    grind [MultiStep, Step] }
  intro hms
  induction hms <;> grind [big_step_implies_step, BigStep]

end Naturals

end Untyped
