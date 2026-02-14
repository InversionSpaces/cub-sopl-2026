/-
5.2.2 : Church Numeral Other Succ

5.2.3 : Church Numeral Mult, No Plus?

5.2.4 : Church Numeral pow

5.2.5 : Subtraction using pred

5.2.6 : Steps to calculate pred

5.2.7 : Equality for Church Numerals

5.2.8 : List implementation in a Lambda Calculus
· Nil, Cons definition
· IsNil, Head definition
· tail definition

5.2.9 : Replace if with test in the definition of g (factorial Church numerals)

5.2.10 : Convert Nat to Church Numeral

5.2.11 : List concatenation operator using Fix

5.3.3 : |FV t| ≤ size t

5.3.6 : Evaluation for Lambda Terms
· full β-reduction
· normal-order
· lazy evaluation

5.3.7 : Extend Wrong (5.3.16) to λNB
⇑ Probably non-trivial

5.3.8 : Big-Step style for λNB
-/
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

namespace LambdaCalculus

namespace Programming

inductive LTerm
| Var (x : Nat)
| Abs (t : LTerm)
| App (t1 : LTerm) (t2 : LTerm)

def lid := LTerm.Abs (.Var 0)

def tru :=
  LTerm.Abs
    (.Abs
      (.Var 0))

def fls :=
  LTerm.Abs
    (.Abs
      (.Var 1))

def test :=
  LTerm.Abs
    (.Abs
      (.Abs
        (.App
          (.App
            (.Var 0)
            (.Var 1))
          (.Var 2))))

def land :=
  LTerm.Abs
    (.Abs
      (.App
        (.App
          (.Var 0)
          (.Var 1))
        fls))

def lor :=
  LTerm.Abs
    (.Abs
      (.App
        (.App
          (.Var 0)
          tru)
        (.Var 1)))

def lnot :=
  LTerm.Abs
    (.App
      (.App
        (.Var 0)
        tru)
      fls)

def lpair :=
  LTerm.Abs
    (.Abs
      (.Abs
        (.App
          (.App
            (.Var 2)
            (.Var 0))
          (.Var 1))))

def fst :=
  LTerm.Abs
    (.App
      (.Var 0)
      tru)

def snd :=
  LTerm.Abs
    (.App
      (.Var 0)
      fls)

def c0 :=
  LTerm.Abs
    (.Abs
      (.Var 1))

def scc :=
  LTerm.Abs
    (.Abs
      (.Abs
        (.App
          (.Var 1)
          (.App
            (.App
              (.Var 0)
              (.Var 1))
            (.Var 2)))))

--5.2.2
def my_scc :=
  LTerm.Abs
    (.Abs
      (.Abs
        (.App
          (.App
            (.Var 0)
            (.Var 1))
          (.App
            (.Var 1)
            (.Var 2)))))

def plus :=
  LTerm.Abs
    (.Abs
      (.Abs
        (.Abs
          (.App
            (.App
              (.Var 0)
              (.Var 2))
            (.App
              (.App
                (.Var 1)
                (.Var 2))
              (.Var 3))))))

def times :=
  LTerm.Abs
    (.Abs
      (.App
        (.App
          (.Var 0)
          (.App
            plus
            (.Var 1)))
        c0))

--5.2.3
def my_times :=
  LTerm.Abs
    (.Abs
      (.App
        (.Var 0)
        (.Var 1)))

end Programming

inductive Term (α : Type) : Type
| Var (x : α)
| Abs (x : α) (t : Term α)
| App (t1 : Term α) (t2 : Term α)

def size : Term α → Nat
| .Var _ => 1
| .Abs _ t => 1 + size t
| .App t1 t2 => 1 + size t1 + size t2

def FV [DecidableEq α] : Term α → Finset α
| .Var x => { x }
| .Abs x t => FV t \ {x}
| .App t1 t2 => FV t1 ∪ FV t2

-- 5.3.3 : |FV t| ≤ size t
def fv_le_size [Countable α] [DecidableEq α] :
  ∀ t : Term α, (FV t).card ≤ size t := by
  intro t
  induction t
  all_goals (grind [FV, size])

def rename [DecidableEq α]
  (t : Term α) (f s : α) : Term α := match t with
  | Term.Var x => if x = f then .Var s else .Var x
  | .Abs x t' => if x = f then .Abs x t' else .Abs x (rename t' f s)
  | .App t1 t2 => .App (rename t1 f s) (rename t2 f s)

lemma rename_size_eq [DecidableEq α] (t : Term α) (f s : α) :
  size (rename t f s) = size t := by
  induction t
  all_goals (grind [rename, size])

class Infinite (α : Type) [DecidableEq α] where
  pick : (s : Finset α) → α
  pick_is_fresh : pick s ∉ s

def subst [DecidableEq α] [Infinite α] : Term α → α → Term α → Term α
| .Var x, f, s => if x = f then s else .Var x
| .Abs x t, f, s =>
  if x = f then .Abs x t
  else if x ∈ FV s then
    let y := Infinite.pick (FV t ∪ FV s ∪ {f})
    .Abs y (subst (rename t x y) f s)
  else .Abs x (subst t f s)
| .App t1 t2, f, s => .App (subst t1 f s) (subst t2 f s)
termination_by t => size t
decreasing_by
  · rw [rename_size_eq]
    grind [size]
  all_goals (grind [size])

inductive AlphaRename [DecidableEq α] : Term α → Term α → Prop
| rename : y ∉ FV t → AlphaRename (.Abs x t) (.Abs y (rename t x y))

inductive CompatClosure (R : Term α → Term α → Prop) : Term α → Term α → Prop
| rel : R t t' → CompatClosure R t t'
| abs : CompatClosure R t t' → CompatClosure R (.Abs x t) (.Abs x t')
| appL : CompatClosure R t t' → CompatClosure R (.App t s) (.App t' s)
| appR : CompatClosure R s s' → CompatClosure R (.App t s) (.App t s')

def AlphaEq [DecidableEq α] : Term α → Term α → Prop :=
  Relation.EqvGen (CompatClosure AlphaRename)

infix:50 " ~a " => AlphaEq

def a_term_setoid [DecidableEq α] : Setoid (Term α)  :=
  Relation.EqvGen.setoid AlphaEq

def ATerm (α : Type) [DecidableEq α] := Quotient (@a_term_setoid α _)

lemma subst_respects_alpha [DecidableEq α] [Infinite α]
  {t t' : Term α} {f : α} {s : Term α} :
  t ~a t' → (subst t f s) ~a (subst t' f s) := by
  intro ha
  induction ha
  · rename_i h
    cases h
    · sorry
    · sorry
    · sorry
    · sorry
  · apply Relation.EqvGen.refl
  · apply Relation.EqvGen.symm
    assumption
  · apply Relation.EqvGen.trans
    repeat assumption

def substA [DecidableEq α] [Infinite α]
  (t : ATerm α) (f : α) (s : Term α) : ATerm α :=
  Quotient.liftOn t
    (fun p => Quotient.mk a_term_setoid (subst p f s))
    (fun a b hav => sorry)

end LambdaCalculus
