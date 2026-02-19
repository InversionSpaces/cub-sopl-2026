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
  | .Var x => if x = f then .Var s else .Var x
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

-- inductive AlphaRename [DecidableEq α] : Term α → Term α → Prop
-- | rename : y ∉ FV t → AlphaRename (.Abs x t) (.Abs y (rename t x y))

-- inductive CompatClosure (R : Term α → Term α → Prop) : Term α → Term α → Prop
-- | rel : R t t' → CompatClosure R t t'
-- | abs : CompatClosure R t t' → CompatClosure R (.Abs x t) (.Abs x t')
-- | appL : CompatClosure R t t' → CompatClosure R (.App t s) (.App t' s)
-- | appR : CompatClosure R s s' → CompatClosure R (.App t s) (.App t s')

-- def AlphaEq [DecidableEq α] : Term α → Term α → Prop :=
--   Relation.EqvGen (CompatClosure AlphaRename)

inductive FreeRename [DecidableEq α] : Term α → Term α → α → α → Prop
| var_rename : FreeRename (.Var f) (.Var s) f s
| var_no_rename : x ≠ f → FreeRename (.Var x) (.Var x) f s
| abs_rename : FreeRename t t' f s → x ≠ f → FreeRename (.Abs x t) (.Abs x t') f s
| abs_stop : FreeRename (.Abs x t) (.Abs x t) x s
| app : FreeRename t1 t1' f s → FreeRename t2 t2' f s → FreeRename (.App t1 t2) (.App t1' t2') f s

lemma rename_correspondance [DecidableEq α] {t t' : Term α} {f s : α} :
  FreeRename t t' f s ↔ rename t f s = t' := by
  constructor
  · intro h
    induction h with
    | var_rename => simp [rename]
    | var_no_rename _ => grind [rename]
    | abs_rename ih _ => grind [rename]
    | abs_stop => simp [rename]
    | app ih1 ih2 => grind [rename]
  · intro h
    induction t
    · grind [FreeRename, rename]
    · simp only [rename] at h
      split_ifs at h
      · grind [FreeRename, rename]
      ·
        sorry
    · simp only [rename] at h
      cases t'
      · contradiction
      · contradiction
      · cases h
        apply FreeRename.app
        ·
          sorry
        sorry

inductive AlphaEq [DecidableEq α] : Term α → Term α → Prop
| refl : AlphaEq t t
| symm : AlphaEq t t' → AlphaEq t' t
| trans : AlphaEq t t' → AlphaEq t' t'' → AlphaEq t t''
| rename: y ∉ FV t → FreeRename t t' x y → AlphaEq (.Abs x t) (.Abs y t')
| appL : AlphaEq t t' → AlphaEq (.App t s) (.App t' s)
| appR : AlphaEq s s' → AlphaEq (.App t s) (.App t s')
| abs : AlphaEq t t' → AlphaEq (.Abs x t) (.Abs x t')

infix:50 " ~a " => AlphaEq

-- def a_term_setoid [DecidableEq α] : Setoid (Term α)  :=
--   Relation.EqvGen.setoid AlphaEq

instance a_term_setoid [DecidableEq α] : Setoid (Term α) where
  r := AlphaEq
  iseqv := by
    constructor
    · apply AlphaEq.refl
    · apply AlphaEq.symm
    · apply AlphaEq.trans

def ATerm (α : Type) [DecidableEq α] := Quotient (@a_term_setoid α _)

inductive SubstRel [DecidableEq α] [Infinite α] : Term α → α → Term α → Term α → Prop
| var :
    SubstRel (.Var f) f s s
| abs_stop :
    SubstRel (.Abs x t) x s (.Abs x t)
| abs_subst :
    SubstRel t f s t' →
    x ≠ f → x ∉ FV s →
    SubstRel (.Abs x t) f s (.Abs x t')
| abs_rename :
    SubstRel t f s t' →
    x ≠ f → y ∉ FV s →
    FreeRename t t' x y →
    SubstRel (.Abs x t) f s (.Abs y t')

lemma subst_correspondance [DecidableEq α] [Infinite α]
  {t t' s : Term α} {f : α} :
  SubstRel t f s t' → subst t f s = t' := by
  intro h
  induction h with
  | var => simp [subst]
  | abs_stop => simp [subst]
  | abs_subst ih _ _ => grind [subst]
  | abs_rename ih _ _ hfr =>
    simp only [subst]
    split_ifs
    · contradiction
    · sorry
    · sorry

-- lemma alpha_var_iff [DecidableEq α] {t t' : Term α}
--   (h : t ~a t') : t = .Var y ↔ t' = .Var y := by
--   induction h with
--   | refl => exact Iff.rfl
--   | symm _ ih => exact ih.symm
--   | trans _ _ ih1 ih2 => exact ih1.trans ih2
--   | rename | appL | appR | abs => exact iff_of_false nofun nofun

-- private def AppDecomp [DecidableEq α] (u v : Term α) : Prop :=
--   ∀ l r, u = .App l r → ∃ l' r', v = .App l' r' ∧ l ~a l' ∧ r ~a r'

-- private lemma alpha_app_chain [DecidableEq α] {u v w : Term α}
--     (f : AppDecomp u v) (g : AppDecomp v w) : AppDecomp u w := by
--   intro l r hlr
--   obtain ⟨l', r', h', hl, hr⟩ := f l r hlr
--   obtain ⟨l'', r'', h'', hl', hr'⟩ := g l' r' h'
--   exact ⟨l'', r'', h'', .trans hl hl', .trans hr hr'⟩

-- private lemma alpha_app_aux [DecidableEq α] {u v : Term α} (h : u ~a v) :
--     AppDecomp u v ∧ AppDecomp v u := by
--   unfold AppDecomp
--   induction h with
--   | refl => constructor <;> aesop (add safe AlphaEq.refl)
--   | symm _ ih => exact ⟨ih.2, ih.1⟩
--   | trans _ _ ih1 ih2 =>
--     exact ⟨alpha_app_chain ih1.1 ih2.1, alpha_app_chain ih2.2 ih1.2⟩
--   | rename => exact ⟨nofun, nofun⟩
--   | appL h _ =>
--     constructor <;> aesop (add safe [AlphaEq.refl, AlphaEq.symm])
--   | appR h _ =>
--     constructor <;> aesop (add safe [AlphaEq.refl, AlphaEq.symm])
--   | abs => exact ⟨nofun, nofun⟩

-- lemma alpha_app [DecidableEq α] {t t1 t2 : Term α} (h : t ~a .App t1 t2) :
--     ∃ s1 s2, t = .App s1 s2 ∧ s1 ~a t1 ∧ s2 ~a t2 := by
--   obtain ⟨s1, s2, hs, h1, h2⟩ := (alpha_app_aux h).2 t1 t2 rfl
--   exact ⟨s1, s2, hs, h1.symm, h2.symm⟩

-- private def AbsDecomp [DecidableEq α] (u v : Term α) : Prop :=
--   ∀ x b, u = .Abs x b → ∃ y b', v = .Abs y b' ∧ (.Abs x b) ~a (.Abs y b')

-- private lemma alpha_abs_chain [DecidableEq α] {u v w : Term α}
--     (f : AbsDecomp u v) (g : AbsDecomp v w) : AbsDecomp u w := by
--   intro x b hxb
--   obtain ⟨y, b', hv, hab⟩ := f x b hxb
--   obtain ⟨z, b'', hw, hab'⟩ := g y b' hv
--   exact ⟨z, b'', hw, .trans hab hab'⟩

-- private lemma alpha_abs_aux [DecidableEq α] {u v : Term α} (h : u ~a v) :
--     AbsDecomp u v ∧ AbsDecomp v u := by
--   unfold AbsDecomp
--   induction h with
--   | refl => constructor <;> aesop (add safe AlphaEq.refl)
--   | symm _ ih => exact ⟨ih.2, ih.1⟩
--   | trans _ _ ih1 ih2 =>
--     exact ⟨alpha_abs_chain ih1.1 ih2.1, alpha_abs_chain ih2.2 ih1.2⟩
--   | rename hfv =>
--     constructor <;> intro _ _ h <;> cases h <;>
--       exact ⟨_, _, rfl, by first | exact .rename hfv | exact .rename (by assumption) (by assumption)⟩
--   | appL | appR => exact ⟨nofun, nofun⟩
--   | abs h _ =>
--     constructor <;>
--       (intro _ _ h'; cases h'; exact ⟨_, _, rfl, by first | exact .abs h | exact .abs (.symm h)⟩)

-- lemma alpha_abs [DecidableEq α] {t : Term α} {x : α} {body : Term α}
--     (h : t ~a .Abs x body) :
--     ∃ y body', t = .Abs y body' ∧ (.Abs y body') ~a (.Abs x body) := by
--   obtain ⟨y, body', hs, hab⟩ := (alpha_abs_aux h).2 x body rfl
--   exact ⟨y, body', hs, hab.symm⟩

-- private lemma rename_fv_sdiff [DecidableEq α]
--   (t : Term α) (x y : α) (hy : y ∉ FV t) :
--     FV (rename t x y) \ {y} = FV t \ {x} := by
--   induction t with
--   | Var z => grind [FV, rename]
--   | Abs z t ih => sorry
--   | App t1 t2 ih1 ih2 => sorry

-- lemma alpha_fv [DecidableEq α] {t t' : Term α}
--     (h : t ~a t') : FV t = FV t' := by
--   induction h with
--   | refl => rfl
--   | symm _ ih => exact ih.symm
--   | trans _ _ ih1 ih2 => exact ih1.trans ih2
--   | appL _ ih => simp [FV, ih]
--   | appR _ ih => simp [FV, ih]
--   | abs _ ih => simp [FV, ih]
--   | rename hfv =>
--     simp only [FV]
--     have := rename_fv_sdiff _ _ _ hfv
--     exact this.symm

-- lemma rename_respects_alpha [DecidableEq α]
--     {t t' : Term α} (h : t ~a t') (a b : α) :
--     rename t a b ~a rename t' a b := by
--   induction h with
--   | refl => exact .refl
--   | symm _ ih => exact .symm ih
--   | trans _ _ ih1 ih2 => exact .trans ih1 ih2
--   | appL _ ih => exact .appL ih
--   | appR _ ih => exact .appR ih
--   | abs h ih =>
--     simp only [rename]
--     split
--     · exact .abs h
--     · exact .abs ih
--   | rename =>
--     sorry

lemma subst_respects_alpha [DecidableEq α] [Infinite α]
  {t t' : Term α} {f : α} {s : Term α} :
  t ~a t' → (subst t f s) ~a (subst t' f s) := by
  intro h
  induction h with
  | refl => exact .refl
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | appL _ ih =>
    simp only [subst]; exact .appL ih
  | appR _ ih =>
    simp only [subst]; exact .appR ih
  | abs h ih =>
    simp only [subst]
    split
    · exact .abs h
    · rename_i hxf
      split
      · sorry
      · exact .abs ih
  | rename hfv =>

    sorry

def substA [DecidableEq α] [Infinite α]
  (t : ATerm α) (f : α) (s : Term α) : ATerm α :=
  Quotient.liftOn t
    (fun p => Quotient.mk a_term_setoid (subst p f s))
    (fun a b hav => sorry)

end LambdaCalculus
