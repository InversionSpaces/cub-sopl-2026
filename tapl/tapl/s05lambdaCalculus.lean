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
import Mathlib.Data.Finset.Max
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
      (.Var 1))

def fls :=
  LTerm.Abs
    (.Abs
      (.Var 0))

def test :=
  LTerm.Abs
    (.Abs
      (.Abs
        (.App
          (.App
            (.Var 2)
            (.Var 1))
          (.Var 0))))

def land :=
  LTerm.Abs
    (.Abs
      (.App
        (.App
          (.Var 1)
          (.Var 0))
        fls))

def lor :=
  LTerm.Abs
    (.Abs
      (.App
        (.App
          (.Var 1)
          tru)
        (.Var 0)))

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
            (.Var 0)
            (.Var 2))
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
      (.Var 0))

def scc :=
  LTerm.Abs
    (.Abs
      (.Abs
        (.App
          (.Var 1)
          (.App
            (.App
              (.Var 2)
              (.Var 1))
            (.Var 0)))))

--5.2.2
def my_scc :=
  LTerm.Abs
    (.Abs
      (.Abs
        (.App
          (.App
            (.Var 2)
            (.Var 1))
          (.App
            (.Var 1)
            (.Var 0)))))

def plus :=
  LTerm.Abs
    (.Abs
      (.Abs
        (.Abs
          (.App
            (.App
              (.Var 3)
              (.Var 1))
            (.App
              (.App
                (.Var 2)
                (.Var 1))
              (.Var 0))))))

def times :=
  LTerm.Abs
    (.Abs
      (.App
        (.App
          (.Var 1)
          (.App
            plus
            (.Var 0)))
        c0))

--5.2.3
def my_times :=
  LTerm.Abs
    (.Abs
      (.App
        (.Var 1)
        (.Var 0)))

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
  let y := Infinite.pick (FV t ∪ FV s ∪ {f})
  if x = f then .Abs x t
  else if x ∈ FV s then
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
| self : AlphaRename t t

inductive CompatClosure (R : Term α → Term α → Prop) : Term α → Term α → Prop
| rel : R t t' → CompatClosure R t t'
| abs : CompatClosure R t t' → CompatClosure R (.Abs x t) (.Abs x t')
| appL : CompatClosure R t t' → CompatClosure R (.App t s) (.App t' s)
| appR : CompatClosure R s s' → CompatClosure R (.App t s) (.App t s')

def AlphaEq [DecidableEq α] : Term α → Term α → Prop :=
  (CompatClosure AlphaRename)

infix:50 " ~a " => AlphaEq

def a_term_setoid [DecidableEq α] : Setoid (Term α)  :=
  Relation.EqvGen.setoid AlphaEq

def ATerm (α : Type) [DecidableEq α] := Quotient (@a_term_setoid α _)

lemma compat_closure_size (t t' : Term α) [DecidableEq α] :
  CompatClosure AlphaRename t t' → size t = size t' := by
    intro h
    unhygienic induction h <;> grind [size, AlphaRename, rename_size_eq]

lemma rename_self (t : Term α) (x : α) [DecidableEq α] :
  rename t x x = t := by
    induction t <;> grind [rename]

lemma compat_trans (t1 t2 t3 : Term α) :
  CompatClosure R t1 t2 → CompatClosure R t2 t3 → CompatClosure R t1 t3 := by
    intro h1 h2
    unhygienic induction t1 generalizing t2 t3
    { cases h1
      sorry }
    { cases h1
      { sorry }
      cases h2
      { sorry }
      sorry }
    sorry

lemma compat_symm (t1 t2 : Term α) :
  CompatClosure R t1 t2 → CompatClosure R t2 t1 := by
    sorry

lemma rename_rename (t : Term α) (x y : α) [DecidableEq α] :
  x ∉ FV t → rename t x y ~a t := by
    intro hx
    unhygienic induction t
    { simp only [rename]
      split
      { grind [FV] }
      apply CompatClosure.rel
      apply AlphaRename.self }
    { simp only [rename]
      split
      { apply CompatClosure.rel
        apply AlphaRename.self }
      have : x ∉ FV t_1 := by grind [FV]
      apply CompatClosure.abs
      aesop }
    rw [rename]
    apply compat_trans
    { apply CompatClosure.appL
      apply t1_ih (by grind [FV]) }
    apply CompatClosure.appR
    exact t2_ih (by grind [FV])

lemma rename_FV (t : Term α) (x y : α) [DecidableEq α] :
  ∀ a, a ∈ FV (rename t x y) → a ∈ FV t ∧ a ≠ x ∨ a = y ∧ x ∈ FV t := by
    unhygienic induction t <;> grind [FV, rename]

lemma induction_size_specified (P : Term α → Prop) :
  ∀ gen_sz, (∀ (s : Term α), (∀ r, size r < size s → P r) → P s) → ∀ s, size s < gen_sz  → P s := by
    intro gen_sz ind s hlt
    induction gen_sz generalizing s <;> grind


lemma induction_size (P : Term α → Prop) :
  (∀ s, (∀ r, size r < size s → P r) → P s) → ∀ t, P t := by
  intro ind s
  exact induction_size_specified P (size s + 1) ind s (by simp)

lemma subst_fv (t : Term α) (f : α) (s : Term α) [DecidableEq α] [Infinite α] :
  f ∉ FV t → t ~a subst t f s := by
    apply induction_size (P := fun t => f ∉ FV t → t ~a subst t f s)
    intro t ind hn
    unhygienic cases t
    { rw [subst]
      have : x ≠ f := by grind [FV]
      rw [if_neg this]
      apply CompatClosure.rel
      apply AlphaRename.self }
    { rw [subst]
      repeat' split
      { apply CompatClosure.rel
        apply AlphaRename.self}
      { simp [FV] at hn
        have lms :=
          AlphaRename.rename (t := t_1) (x := x) (y := Infinite.pick (FV t_1 ∪ FV s ∪ {f}))
            (by grind [Infinite.pick_is_fresh])
        apply compat_trans
        { apply CompatClosure.rel
          apply lms }
        apply CompatClosure.abs
        apply ind (rename t_1 x (Infinite.pick (FV t_1 ∪ FV s ∪ {f})))
          (by grind [size, rename_size_eq])
        intro hts
        have st := rename_FV t_1 x (Infinite.pick (FV t_1 ∪ FV s ∪ {f})) f hts
        grind [Infinite.pick_is_fresh] }
      apply CompatClosure.abs
      apply ind t_1 (by simp [size])
      grind [FV] }
    rw [subst]
    apply compat_trans
    { apply CompatClosure.appL
      apply ind t1 (by grind [size]) (by grind [FV]) }
    apply CompatClosure.appR
    apply ind t2 (by grind [size]) (by grind [FV])

lemma subst_respects_alpha [DecidableEq α] [Infinite α]
  {t t' : Term α} {f : α} {s : Term α} :
  t ~a t' → (subst t f s) ~a (subst t' f s) := by
  apply induction_size (P := fun t => ∀ t', t ~a t' → (subst t f s) ~a (subst t' f s))
  intro t ind t' ha
  unhygienic cases t
  { unhygienic cases ha
    cases a
    apply CompatClosure.rel
    apply AlphaRename.self }
  { unhygienic cases ha
    { unhygienic cases a
      { rw [subst]
        split_ifs with h
        { rw [subst]
          split_ifs with h1
          { apply CompatClosure.rel
            apply AlphaRename.rename a_1 }
          { apply compat_symm
            apply compat_trans
            { apply CompatClosure.abs
              apply compat_symm
              apply subst_fv _ f s
              intro contra
              unhygienic cases rename_FV _ _ _ f contra
              { cases rename_FV _ _ _ f h_1.1 <;> grind }
              grind [Infinite.pick_is_fresh] }
            apply compat_trans
            { apply compat_symm
              apply CompatClosure.rel
              apply AlphaRename.rename
              intro contra
              cases rename_FV _ _ _ _ contra <;> grind [Infinite.pick_is_fresh] }
            apply compat_symm
            apply CompatClosure.rel
            apply AlphaRename.rename a_1 }
          apply compat_trans
          { apply CompatClosure.rel
            apply AlphaRename.rename (y := y) a_1 }
          apply CompatClosure.abs
          apply subst_fv
          intro contra
          have := rename_FV t_1 x y f contra
          grind }
        { rw [subst]
          split_ifs with h1
          { apply compat_trans
            { apply compat_symm
              apply CompatClosure.abs
              apply subst_fv
              intro contra
              cases rename_FV _ _ _ _ contra
              { grind }
              grind [Infinite.pick_is_fresh] }
            apply compat_symm
            apply compat_trans
            { apply CompatClosure.rel
              apply AlphaRename.rename (y := (Infinite.pick (FV t_1 ∪ FV s ∪ {f})))
              intro contra
              cases rename_FV _ _ _ _ contra <;> grind [Infinite.pick_is_fresh] }
            apply compat_trans
            { apply compat_symm
              apply CompatClosure.rel
              apply AlphaRename.rename
              intro contra
              cases rename_FV _ _ _ _ contra <;> grind [Infinite.pick_is_fresh] }
            apply compat_symm
            apply compat_trans
            { apply compat_symm
              apply CompatClosure.rel
              apply AlphaRename.rename
              grind [Infinite.pick_is_fresh] }
            apply CompatClosure.rel
            apply AlphaRename.rename
            grind [Infinite.pick_is_fresh] }
          { apply compat_trans
            { apply CompatClosure.abs
              stop sorry }
            sorry }
          stop sorry }
        rw [subst]
        split_ifs with h1 h2
        stop sorry }
      apply CompatClosure.rel
      apply AlphaRename.self }
    rw [subst, subst]
    split_ifs with h1 h2
    { apply CompatClosure.abs
      apply a }
    { apply compat_trans
      { apply CompatClosure.rel
        apply AlphaRename.rename (y := Infinite.pick (FV t_1 ∪ FV t'_1 ∪ FV s ∪ {f}))

        sorry }
      apply compat_symm
      apply compat_trans
      { apply CompatClosure.rel
        apply AlphaRename.rename (y := Infinite.pick (FV t_1 ∪ FV t'_1 ∪ FV s ∪ {f}))
        sorry }
      apply CompatClosure.abs

      have := ind t_1 (by grind [size]) t'_1 a
      sorry }
    apply CompatClosure.abs
    apply ind t_1 (by grind [size]) t'_1 a }
  rw [subst]
  unhygienic cases ha
  { cases a
    rw [subst]
    apply CompatClosure.rel
    apply AlphaRename.self }
  { rw [subst]
    apply CompatClosure.appL
    apply ind t1 (by grind [size])
    exact a }
  rw [subst]
  apply CompatClosure.appR
  apply ind t2 (by grind [size])
  exact a
  /-unhygienic induction ha
  { unhygienic cases a
    { rw [subst, subst]
      repeat' unhygienic split
      { rename_i h1 h2
        rw [h1, h2, rename_self]
        apply CompatClosure.rel
        apply AlphaRename.self }
      { sorry }
      { sorry }
      { sorry }
      { sorry }
      { sorry }
      { sorry }
      { sorry }
      stop sorry }
    apply CompatClosure.rel
    apply AlphaRename.self }
  { rw [subst, subst]
    repeat' unhygienic split
    { apply CompatClosure.abs
      exact a }
    { have y := Infinite.pick (FV t_1 ∪ FV s ∪ {f})
      have st :
        Term.Abs y (subst (rename t_1 x y) f s) =
        Term.Abs y (rename (subst t_1 f s) x y) := by

          sorry
      have :
        Term.Abs y (subst (rename t_1 x y) f s) ~a
        Term.Abs y (subst t_1 f s) := by


          sorry
      sorry }
    apply CompatClosure.abs
    exact a_ih }
  { rw [subst, subst]
    apply CompatClosure.appL
    exact a_ih }
  rw [subst, subst]
  apply CompatClosure.appR
  exact a_ih-/

def substA [DecidableEq α] [Infinite α]
  (t : ATerm α) (f : α) (s : Term α) : ATerm α :=
  Quotient.liftOn t
    (fun p => Quotient.mk a_term_setoid (subst p f s))
    (fun a b hav => sorry)

end LambdaCalculus
