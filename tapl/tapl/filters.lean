import Mathlib.Tactic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith

namespace FilterModel

inductive Term
| Var (x : Nat) : Term
| Abs (t : Term) : Term
| App (t1 : Term) (t2 : Term) : Term

inductive FV : Term → Nat → Prop
| Var : x < n → FV (.Var x) n
| Abs (t : Term) (h : FV t n.succ) : FV (.Abs t) n
| App (t1 : Term) (t2 : Term)
          (h1 : FV t1 n) (h2 : FV t2 n) : FV (t1.App t2) n

def shift_up_from (c : Nat) : Term → Term
| .Var x => if x < c then .Var x else .Var (x + 1)
| .Abs t => .Abs (shift_up_from (c + 1) t)
| .App t1 t2 => .App (shift_up_from c t1) (shift_up_from c t2)

def shift_up (s : Term) : Term := shift_up_from 0 s

def betar (k : Nat) (t s : Term) : Term :=
  match t with
  | .Var x => if x = k then s else if x < k then .Var x else .Var (x - 1)
  | .Abs t1 => .Abs (betar (k + 1) t1 (shift_up s))
  | .App t1 t2 => (betar k t1 s).App (betar k t2 s)

abbrev subst (t s : Term) : Term := betar 0 t s

inductive Step : Term → Term → Prop
| AppL (t t' s : Term) :
  Step t t' →
  Step (t.App s) (t'.App s)
| AppR (t s' s : Term) :
  Step s s' →
  Step (t.App s) (t.App s')
| Abs (t t' : Term) :
  Step t t' →
  Step (.Abs t) (.Abs t')
| Beta (t s : Term) :
  Step ((t.Abs).App s) (subst t s)

inductive BetaEquiv : Term → Term → Prop
| Refl (t : Term) : BetaEquiv t t
| Symm (t1 t2 : Term) : BetaEquiv t1 t2 → BetaEquiv t2 t1
| Trans (t1 t2 t3 : Term) : BetaEquiv t1 t2 → BetaEquiv t2 t3 → BetaEquiv t1 t3
| Step (t1 t2 : Term) : Step t1 t2 → BetaEquiv t1 t2

def TermFV (n : Nat) := {t : Term // FV t n}

abbrev TermFV.abs (t : TermFV n.succ) : TermFV n :=
  ⟨.Abs t.val, by grind [FV]⟩

abbrev TermFV.var (x : Fin n) : TermFV n :=
  ⟨.Var x.val, by grind [FV]⟩

abbrev TermFV.app (t1 t2 : TermFV n) : TermFV n :=
  ⟨.App t1.val t2.val, by grind [FV]⟩

def Term.fv_set : Term → Set Nat
| .Var x => {x}
| .Abs t => t.fv_set \ {0} |>.image (Nat.pred)
| .App t1 t2 => t1.fv_set ∪ t2.fv_set

lemma fv_set_sound (h : FV t n) : ∀ x ∈ t.fv_set, x < n := by
  induction t generalizing n <;> cases h
  · intro x hx
    cases hx
    assumption
  · intro x hx
    rcases hx with ⟨ w, _, _⟩
    by_cases h0 : w = 0
    · grind [Set.mem_diff w]
    · grind [Nat.succ_pred_eq_of_ne_zero h0]
  · intro x hx
    cases hx <;> grind

def TermFV.fv_set (t : TermFV n) : Set (Fin n) :=
  { x : Fin n | x.val ∈ t.val.fv_set }

def VarInt (D : Type) (n : Nat) := Fin n → D

def VarInt.insert (vi : VarInt D n) (d : D) : VarInt D n.succ
| ⟨0, _⟩ => d
| ⟨m + 1, h⟩ => vi ⟨m, by grind⟩

structure LambdaModel where
  D : Type
  app : D → D → D
  int : TermFV n → VarInt D n → D
  vars : ∀ vi : VarInt D n, ∀ m : Fin n,
      int (TermFV.var m) vi = vi m
  apps : ∀ t1 t2 : TermFV n, ∀ vi : VarInt D n,
    int (t1.app t2) vi = app (int t1 vi) (int t2 vi)
  betas : ∀ t : TermFV n.succ, ∀ d : D, ∀ vi : VarInt D n,
    app (int t.abs vi) d = int t (vi.insert d)
  vi_irrel : ∀ t : TermFV n, ∀ vi1 vi2 : VarInt D n,
    (∀ x ∈ t.fv_set, vi1 x = vi2 x) →
      int t vi1 = int t vi2
  abs_irrel : ∀ t1 t2 : TermFV n.succ, ∀ vi : VarInt D n,
    (∀ d : D, int t1 (vi.insert d) = int t2 (vi.insert d)) →
      int t1.abs vi = int t2.abs vi

namespace Curry

inductive TypeScheme
| var (i : Nat) : TypeScheme
| arrow (s t : TypeScheme) : TypeScheme

abbrev Basis := List TypeScheme

inductive TypeAssgn : Basis → TypeScheme → Term → Prop
| base (B : Basis) (ts : TypeScheme) (n : Nat) :
  B[n]? = some ts → TypeAssgn B ts (.Var n)
| abs (B : Basis) (tsa tsr : TypeScheme) (t : Term) :
  TypeAssgn (tsa :: B) tsr t →
  TypeAssgn B (tsa.arrow tsr) (.Abs t)
| app (B : Basis) (tsa tsr : TypeScheme) (t1 t2 : Term) :
  TypeAssgn B (tsa.arrow tsr) t1 →
  TypeAssgn B tsa t2 →
  TypeAssgn B tsr (t1.App t2)

end Curry

end FilterModel
