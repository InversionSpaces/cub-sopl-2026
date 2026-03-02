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

def bred (s t : BLTerm) : BLTerm :=
  shift_down (subst (shift_up s) t)

inductive SmallStep : BLTerm → BLTerm → Prop
| appL : SmallStep t1 t1' → SmallStep (.App t1 t2) (.App t1' t2)
| beta : SmallStep (.App (.Abs t1) t2) (bred t2 t1)

lemma shift_up_from_fv (t : BLTerm) (h : t.FVn n) :
  (shift_up_from m t).FVn (n + 1) := by
  induction t generalizing n m <;> cases h
  · simp only [shift_up_from]
    split_ifs with h
    all_goals (grind [BLTerm.FVn.var])
  · rename_i ih b
    apply BLTerm.FVn.abs
    apply ih
    assumption
  · rename_i ih1 ih2 fv1 fv2
    apply BLTerm.FVn.app
    · grind
    · grind

lemma shift_up_fv (t : BLTerm) (h : t.FVn n) : (shift_up t).FVn (n + 1) :=
  shift_up_from_fv t h

lemma shifts_from_cancel : shift_down_from m (shift_up_from m t) = t := by
  induction t generalizing m
  · simp only [shift_up_from]
    split_ifs with h
    · grind [shift_down_from]
    · simp only [shift_down_from]
      rw [if_neg (by grind)]
      rfl
  · simp only [shift_up_from, shift_down_from]
    grind
  · simp only [shift_up_from, shift_down_from]
    grind

lemma shifts_cancel : shift_down (shift_up t) = t := by
  apply shifts_from_cancel

lemma bred_preserves_fv (t s : BLTerm)
  (fvt : t.FVn (n + 1)) (fvs : s.FVn n) : (bred s t).FVn n := by
  induction t <;> cases fvt
  · simp only [bred, subst, substN]
    split_ifs with h
    · rw [shifts_cancel]
      assumption
    · simp only [shift_down, shift_down_from]
      rw [if_neg (by grind)]
      apply BLTerm.FVn.var
      grind [Nat.pred_eq_sub_one]
  ·
    sorry
  · sorry

lemma step_preserves_fv (h : SmallStep t t') :
  ∀ n, t.FVn n → t'.FVn n := by
  induction t generalizing t' <;> cases h
  · rename_i t1ih t2ih t1' step
    intro n hfv
    cases hfv
    constructor
    · apply t1ih
      · assumption
      · assumption
    · assumption
  · rename_i t2 t2ih t1 t1ih
    intro n hfv
    cases hfv
    rename_i hfvt1a _
    cases hfvt1a

    sorry

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

mutual
inductive EvalCtxN : Nat → Type where
| mk (ctx : Fin n → Σ m : Nat, CloN m) : EvalCtxN n

inductive ValCloN : Nat → Type where
| mk (p : BLTerm) (hv : Value p) (fvh : p.FVn n)
      (ctx : EvalCtxN n) : ValCloN n

inductive CloN : Nat → Type where
| mk (p : BLTerm) (fvh : p.FVn n) (ctx : EvalCtxN n) : CloN n
end

abbrev ValClo := Σ n: Nat, ValCloN n
abbrev Clo := Σ n: Nat, CloN n
abbrev EvalCtx := Σ n: Nat, EvalCtxN n

abbrev EvalCtx.n : EvalCtx → Nat
| ⟨n, _⟩ => n

abbrev EvalCtxN.get (ctx : EvalCtxN n) (i : Fin n) : Clo :=
  match ctx with
  | EvalCtxN.mk fn => fn i

abbrev EvalCtx.get (ctx : EvalCtx) (i : Fin ctx.n) : Clo :=
  match ctx with
  | ⟨_, EvalCtxN.mk fn⟩ => fn i

def ctx_of (fn : Fin n → Clo) : EvalCtxN n :=
  .mk (fun i => fn i)

def EvalCtxN.subst (ctx : EvalCtxN n) (s : Clo) : EvalCtxN (n.succ) :=
  ctx_of (fun i => match i with
    | ⟨ 0, _⟩ => s
    | ⟨ i + 1, h⟩ => ctx.get ⟨i, by grind⟩
  )

inductive Eval : Clo → ValClo → Prop where
| var {ctx : EvalCtxN n} :
  Eval (ctx.get x) v →
  Eval ⟨ n, .mk (.Var x.val) (by grind [BLTerm.FVn.var]) ctx ⟩ v
| lam :
  Eval ⟨n, .mk (.Abs t) f (.mk c)⟩
       ⟨n, .mk (.Abs t) Value.abs f (.mk c)⟩
| app :
  Eval ⟨ n1, .mk e1 p c⟩ ⟨ n, .mk (.Abs e) q r c'⟩ →
  Eval ⟨ n + 1, .mk e u (c'.subst v) ⟩ v' →
  Eval ⟨ n1, .mk (.App e1 e2) w c⟩ v'

lemma steps_impl_eval
  (steps : MultiStep t v) (hfv : t.FVn n) (hval : Value v) :
  ∀ ctx : EvalCtxN n, ∃ rctx : EvalCtxN m,
  Eval ⟨ n, .mk t hfv ctx ⟩ ⟨ n, .mk v hval hfvv ctx ⟩ := by
  induction steps
  · intro ctx
    cases hval
    · rename_i x
      use ctx_of (fun i => by sorry)
      apply Eval.var

      sorry
    · sorry
  · sorry


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

namespace Simulation

mutual
inductive EvalCtxN : Nat → Type where
| mk (ctx : Fin n → Σ m : Nat, ValCloN m) : EvalCtxN n

inductive ValCloN : Nat → Type where
| mk (p : BLTerm) (hv : Value p) (fvh : p.FVn n)
      (ctx : EvalCtxN n) : ValCloN n

inductive CloN : Nat → Type where
| mk (p : BLTerm) (fvh : p.FVn n) (ctx : EvalCtxN n) : CloN n
end

abbrev ValClo := Σ n: Nat, ValCloN n
abbrev Clo := Σ n: Nat, CloN n
abbrev EvalCtx := Σ n: Nat, EvalCtxN n

abbrev EvalCtx.n : EvalCtx → Nat
| ⟨n, _⟩ => n

abbrev EvalCtxN.get (ctx : EvalCtxN n) (i : Fin n) : ValClo :=
  match ctx with
  | EvalCtxN.mk fn => fn i

abbrev EvalCtx.get (ctx : EvalCtx) (i : Fin ctx.n) : ValClo :=
  match ctx with
  | ⟨_, EvalCtxN.mk fn⟩ => fn i

def ctx_of (fn : Fin n → ValClo) : EvalCtxN n :=
  .mk (fun i => fn i)

def EvalCtxN.subst (ctx : EvalCtxN n) (s : ValClo) : EvalCtxN (n.succ) :=
  ctx_of (fun i => match i with
    | ⟨ 0, _⟩ => s
    | ⟨ i + 1, h⟩ => ctx.get ⟨i, by grind⟩
  )

inductive Eval : Clo → ValClo → Prop where
| var :
  Eval ⟨n, .mk (.Var k) (BLTerm.FVn.var h) (.mk c) ⟩
       (c (Fin.mk k h))
| lam :
  Eval ⟨n, .mk (.Abs t) f (.mk c)⟩
       ⟨n, .mk (.Abs t) Value.abs f (.mk c)⟩
| app :
  Eval ⟨ n1, .mk e1 p c⟩ ⟨ n, .mk (.Abs e) q r c'⟩ →
  Eval ⟨ n1, .mk e2 s c⟩ v →
  Eval ⟨ n + 1, .mk e u (c'.subst v) ⟩ v' →
  Eval ⟨ n1, .mk (.App e1 e2) w c⟩ v'

end Simulation

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

lemma cbn_cbv_value_eq : CBNameV t ↔ CBValueV t := by
  constructor
  · intro hv
    cases hv
    repeat constructor
  · intro hv
    cases hv
    repeat constructor


def shift_up_from_iter (k : Nat) (s : BLTerm) :=
  match k with
  | 0 => shift_up s
  | k_1 + 1 => shift_up (shift_up_from_iter k_1 s)


def shift_up_iter (k : Nat) (s : BLTerm) :=
  match k with
  | 0 => s
  | k_1 + 1 => shift_up (shift_up_iter k_1 s)

def shift_down_from_iter (k : Nat) (n : Nat) (s : BLTerm) :=
  match k with
  | 0 => shift_down_from n s
  | k_1 + 1 => shift_down (shift_down_from_iter k_1 n s)

def betar (k : Nat) (t s : BLTerm) : BLTerm :=
  match t with
  | .Var x => if x = k then s else if x < k then .Var x else .Var x.pred
  | .Abs t1 => (betar (k + 1) t1 (shift_up s)).Abs
  | .App t1 t2 => (betar k t1 s).App (betar k t2 s)

def beta_red (k : ℕ) (t s : BLTerm) :=
  shift_down_from k (substN k (shift_up_from k s) t)

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
    rw [beta_red, beta_red, substN, shift_down_from]
    rfl

lemma shift_comp_one :
  shift_up_from d (shift_up_from (k + d) t) = shift_up_from (k + d + 1) (shift_up_from d t) := by
  unhygienic induction t generalizing d <;> grind [shift_up, shift_up_from]

lemma beta_eq (t s : BLTerm) :
  beta_red k t s = betar k t s := by
    unhygienic induction t generalizing s k
    { rw [beta_red, betar, substN]
      grind [shift_up_from, substN, shift_down_from, Nat.pred_eq_sub_one, shift_up_down] }
    { rw [beta_red, substN]
      rw [betar, shift_down_from]
      have eq_lemma := shift_comp_one (d := 0) (t := s) (k := k)
      grind [shift_up, beta_red] }
    rw [beta_dist, betar]
    grind


inductive SStep : BLTerm → BLTerm → Prop
| abs : SStep t t' → SStep (.Abs t) (.Abs t')
| appl : SStep t t' → SStep (.App t s) (.App t' s)
| appr : SStep s s' → SStep (.App t s) (.App t s')
| beta : SStep (.App (.Abs t) s) (betar 0 t s)

inductive MultiSStep : BLTerm → BLTerm → Prop
| refl : MultiSStep s s
| step : MultiSStep s1 s2 → SStep s s1 → MultiSStep s s2

lemma ms_trans :
  MultiSStep t t1 → MultiSStep t1 t2 → MultiSStep t t2 := by
    intro h1 h2
    unhygienic induction h1
    { exact h2 }
    apply MultiSStep.step
    { apply a_ih h2 }
    exact a_1

lemma ms_app :
  MultiSStep t t' → MultiSStep s s' → MultiSStep (t.App s) (t'.App s') := by
    intro ht hs
    apply ms_trans (t1 := t'.App s)
    { unhygienic induction ht
      { apply MultiSStep.refl }
      apply MultiSStep.step
      { apply a_ih }
      grind [SStep] }
    unhygienic induction hs
    { apply MultiSStep.refl }
    apply MultiSStep.step
    { apply a_ih }
    grind [SStep]

lemma ms_abs :
  MultiSStep t t' → MultiSStep t.Abs t'.Abs := by
    intro ht
    unhygienic induction ht
    { apply MultiSStep.refl }
    apply MultiSStep.step
    { apply a_ih }
    grind [SStep]

lemma shift_comp :
  shift_up_iter d (shift_up_from k s) = shift_up_from (k + d) (shift_up_iter d s) := by
  unhygienic induction d generalizing k s
  { grind [shift_up_iter] }
  repeat rw [shift_up_iter]
  rw [a, shift_up, shift_up]
  have := shift_comp_one (d := 0) (k := k + n) (t := (shift_up_iter n s))
  grind

lemma beta_shift_lemma_gen (t s : BLTerm) (d : Nat) :
  (betar d (shift_up_from (k + 1 + d) t) (shift_up_iter d (shift_up_from k s))) =
  shift_up_from (k + d) (betar d t (shift_up_iter d s)) := by
    unhygienic induction t generalizing d
    { rw [shift_up_from]
      split_ifs
      { rw [betar, betar]
        split_ifs
        { apply shift_comp }
        { rw [shift_up_from]
          grind }
        grind [shift_up_from, Nat.pred_eq_sub_one] }
      rw [betar, betar]
      split_ifs <;> try grind [shift_up_from, Nat.pred_eq_sub_one] }
    { rw [shift_up_from, betar, betar, shift_up_from]
      have ih := t_ih (d := d + 1)
      rw [shift_up_iter, shift_up_iter] at ih
      grind }
    rw [betar, shift_up_from, betar, shift_up_from]
    grind

lemma shift_up_step (s s' : BLTerm) :
  SStep s s' → SStep (shift_up_from k s) (shift_up_from k s') := by
    intro hs
    unhygienic induction hs generalizing k
    { repeat rw [shift_up_from]
      grind [SStep] }
    { rw [shift_up_from, shift_up_from]
      grind [SStep] }
    { rw [shift_up_from, shift_up_from]
      grind [SStep] }
    repeat rw [shift_up_from]
    have := SStep.beta (t := (shift_up_from (k + 1) t)) (s := (shift_up_from k s_1))
    have eq := beta_shift_lemma_gen t s_1 0 (k := k)
    simp only [add_zero, shift_up_iter] at eq
    rw [eq] at this
    exact this

lemma shift_beta_one (d k : Nat) (s_1 s : BLTerm) :
  shift_up_from d (betar (k + d) s_1 (shift_up_iter d s)) =
  betar (k + d + 1) (shift_up_from d s_1) (shift_up_iter d (shift_up_from 0 s)) := by
  unhygienic induction s_1 generalizing d
  { rw [betar, shift_up_from]
    split_ifs <;> try grind [betar, shift_up_iter, Nat.pred_eq_sub_one, shift_up_from]
    rw [betar]
    split_ifs <;> try omega
    simp [shift_comp] }
  { simp only [betar, shift_up_from]
    have ih := t_ih (d := d + 1)
    grind [shift_up_iter] }
  grind [betar, shift_up_from]

lemma shift_iter_beta :
  shift_up_iter d (betar k s_1 s) =
  betar (k + d) (shift_up_iter d s_1) (shift_up_iter d s) := by
  unhygienic induction d
  { grind [shift_up_iter] }
  repeat rw [shift_up_iter]
  rw [a]
  have := shift_beta_one 0 (k + n) (shift_up_iter n s_1) (shift_up_iter n s)
  repeat rw [shift_up]
  repeat rw [shift_up_iter] at this
  grind

def shift_iter_dir (k d : Nat) : BLTerm → BLTerm
| .Var x => if x < k then .Var x else .Var (x + d)
| .Abs t => (shift_iter_dir (k + 1) d t).Abs
| .App t1 t2 => (shift_iter_dir k d t1).App (shift_iter_dir k d t2)

lemma inner_shift_iter (d : Nat) (t : BLTerm) :
  shift_up_iter (d + 1) t = shift_up_iter d (shift_up t) := by
    induction d <;> grind [shift_up_iter]

lemma shift_iter_eq (d : Nat) (t : BLTerm) :
  shift_iter_dir 0 d t = shift_up_iter d t := by
    unhygienic induction d generalizing t
    { rw [shift_up_iter]
      have zero_lem :
        ∀ k,
        shift_iter_dir k 0 t = t := by
          induction t <;> grind [shift_iter_dir]
      rw [zero_lem] }
    rw [inner_shift_iter]
    rw [←a]
    rw [shift_up]
    have zero_stat:
      ∀ k,
        shift_iter_dir k (n + 1) t = shift_iter_dir k n (shift_up_from k t) := by
        unhygienic induction t <;> grind [shift_iter_dir, shift_up_from]
    rw [zero_stat]

lemma beta_shift_iter (d : Nat) :
  betar d (shift_up_iter (d + 1) t) s = shift_up_iter d t := by
    repeat rw [←shift_iter_eq]
    have gen_lemma :
      ∀ k,
      betar (d + k) (shift_iter_dir k (d + 1) t) s = shift_iter_dir k d t := by
        intro k
        unhygienic induction t generalizing k s
        { grind [shift_iter_dir, betar, Nat.pred_eq_sub_one] }
        { repeat rw [shift_iter_dir]
          rw [betar]
          have := t_ih (s := shift_up s)
          grind }
        grind [betar, shift_iter_dir]
    grind

lemma beta_beta (d : Nat) (t_1 s s_1 : BLTerm) :
  (betar d
    (betar (k + d + 1) t_1 (shift_up (shift_up_iter d s)))
    (shift_up_iter d (betar k s_1 s))) =
  (betar (k + d) (betar d t_1 (shift_up_iter d s_1)) (shift_up_iter d s)) := by
    unhygienic induction t_1 generalizing d
    { repeat rw [betar]
      split_ifs <;> try grind [Nat.pred_eq_sub_one, betar]
      { rw [betar]
        split_ifs <;> try grind [Nat.pred_eq_sub_one]
        have := beta_shift_iter d (t := s) (s := (shift_up_iter d (betar k s_1 s)))
        rw [shift_up_iter] at this
        rw [this] }
      rw [betar, if_pos]
      { rw [shift_iter_beta] }
      omega }
    { repeat rw [betar]
      have ih := t_ih (d := d + 1)
      grind [shift_up_iter] }
    repeat rw [betar]
    grind

lemma beta_step_l (k : Nat) (t t' s : BLTerm) :
  SStep t t' → SStep (betar k t s) (betar k t' s) := by
    intro ht
    unhygienic induction ht generalizing s k
    { rw [betar, betar]
      grind [SStep] }
    { rw [betar, betar]
      grind [SStep] }
    { rw [betar, betar]
      grind [SStep] }
    rw [betar, betar]
    rename_i s_1
    have := SStep.beta (t := (betar (k + 1) t_1 (shift_up s))) (s := (betar k s_1 s))
    have lemma_2 := beta_beta 0 t_1 s s_1 (k := k)
    simp only [add_zero, shift_up_iter] at lemma_2
    grind

lemma beta_step_r (t s s' : BLTerm) (k : Nat) :
  MultiSStep s s' → MultiSStep (betar k t s) (betar k t s') := by
    intro ht
    unhygienic induction t generalizing s s' k
    { rw [betar, betar]
      split_ifs
      { apply ht }
      { apply MultiSStep.refl }
      apply MultiSStep.refl }
    { rw [betar, betar]
      apply ms_abs
      apply t_ih (shift_up s) (shift_up s') _
      rw [shift_up, shift_up]
      unhygienic induction ht
      { apply MultiSStep.refl }
      apply MultiSStep.step
      { apply a_ih }
      apply shift_up_step
      apply a_1 }
    rw [betar, betar]
    apply ms_app <;> grind

theorem step_diamond (s t1 t2 : BLTerm) :
  SStep s t1 → SStep s t2 → ∃ r, MultiSStep t1 r ∧ MultiSStep t2 r := by
    intro h1 h2
    unhygienic induction h1 generalizing t2 <;> unhygienic cases h2
    { rcases a_ih t'_1 a_1 with ⟨r, hr⟩
      exists r.Abs
      grind [ms_abs] }
    { rcases a_ih t'_1 a_1 with ⟨r, hr⟩
      exists r.App s_1
      grind [ms_app, MultiSStep] }
    { exists t'.App s'
      grind [ms_app, MultiSStep] }
    { unhygienic cases a
      exists betar 0 t'_1 s_1
      constructor
      { apply MultiSStep.step
        { apply MultiSStep.refl }
        apply SStep.beta }
      apply MultiSStep.step
      { apply MultiSStep.refl }
      apply beta_step_l _ _ _ _ a_1 }
    { exists t'.App s'
      grind [MultiSStep, ms_app] }
    { rcases a_ih s'_1 a_1 with ⟨r, hr⟩
      exists t.App r
      grind [MultiSStep, ms_app] }
    { exists betar 0 t_1 s'
      constructor
      { apply MultiSStep.step
        { apply MultiSStep.refl }
        apply SStep.beta }
      have := MultiSStep.step (MultiSStep.refl) a
      apply beta_step_r _ _ _ _ this }
    { unhygienic cases a
      exists betar 0 t'_1 s_1
      constructor
      { apply MultiSStep.step
        { apply MultiSStep.refl }
        apply beta_step_l _ _ _ _ a_1 }
      apply MultiSStep.step
      { apply MultiSStep.refl }
      apply SStep.beta }
    { exists betar 0 t s'
      constructor
      { have := MultiSStep.step (MultiSStep.refl) a
        apply beta_step_r _ _ _ _ this }
      apply MultiSStep.step
      { apply MultiSStep.refl }
      apply SStep.beta }
    exists betar 0 t s_1
    grind [MultiSStep.refl]

theorem multistep_diamond (s t1 t2 : BLTerm) :
  MultiSStep s t1 → MultiSStep s t2 → ∃ r, MultiSStep t1 r ∧ MultiSStep t2 r := by
    intro h1 h2
    unhygienic induction h1 generalizing t2
    { exists t2
      grind [MultiSStep] }
    unhygienic induction h2 generalizing s2 s1
    { exists s2
      grind [MultiSStep] }
    rename_i s3 s4 hms hs ih
    rcases step_diamond s_2 _ _ hs a_1 with ⟨r, hr1, hr2⟩
    rcases a_ih _ hr2 with ⟨r1, hr3⟩
    have : MultiSStep s3 r1 := by
      apply ms_trans
      { apply hr1 }
      apply hr3.2
    unhygienic cases this
    { exists s4
      grind [ms_trans, MultiSStep] }

    rcases ih (s2 := r1) (s1 := s1_1) a_2 a_3
      (by
        intro t3 ht3
        sorry) with ⟨ans, hans⟩
    exists ans
    grind [ms_trans]
