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
  (remove_names ctx t).FVn ctx.length  := by
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

def subst (j : ℕ) (s : BLTerm) : BLTerm → BLTerm
| .Var x => if x = j then s else .Var x
| .Abs t => .Abs (subst (j + 1) (shift_up s) t)
| .App t1 t2 => .App (subst j s t1) (subst j s t2)

end Semantics

end Nameless
