import Mathlib.Tactic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.AList

namespace Subtyping

abbrev Label := String

#check List.Nodup

structure SList (α : Type*) [DecidableEq α] [Inhabited α] where
  elems : List α
  nodup : elems.Nodup


instance (α : Type*) [DecidableEq α] [Inhabited α] : Inhabited (SList α) where
  default := ⟨[], by simp⟩

inductive type
| boolean
| nat
| arr (tp : type) (ct : type)
| rcd (tps : List type) (tpl : SList Label)
| top
deriving Inhabited

inductive Term
| trueT : Term
| falseT : Term
| ite (ct : Term) (t₁ : Term) (t₂ : Term) : Term
| Var (x : Nat)
| Abs (t : Term) (tp : type)
| App (t₁ : Term) (t₂ : Term)
| Zero
| Succ (t : Term)
| Pred (t : Term)
| IsZero (t : Term)
| Rcd (tpt : List Term) (tpl : SList Label)
| Proj (t : Term) (l : Label)
deriving Inhabited

inductive NatValue : Term → Prop
| ZeroV : NatValue .Zero
| SuccV (t : Term) : NatValue t → NatValue (.Succ t)

inductive Value : Term → Prop
| Abs (t : Term) (tp : type) : Value (t.Abs tp)
| trueV : Value .trueT
| falseV : Value .falseT
| NatV (t : Term) : NatValue t → Value t
| RcdV (tpt : List Term) (tpl : SList Label) :
  (∀ i < tpt.length, Value tpt[i]!) →
  Value (Term.Rcd tpt tpl)

abbrev TCtx := List type

@[simp, grind]
def TCtx.types (Γ : TCtx) (x : Nat) (tp : type) : Prop := Γ[x]? = tp

-- For keys specifically
theorem SList.Perm.key_correspondence [DecidableEq α] [Inhabited α]
    (s t : SList α) (h : s.elems.Perm t.elems)
    (i : Fin s.elems.length) :
    ∃ j : Fin t.elems.length,
      s.elems[i]! = t.elems[j]! := by
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp (h.mem_iff.mp (List.getElem_mem i.isLt))
  exact ⟨⟨j, hj⟩, by grind⟩

inductive Typ : TCtx → Term → type → Prop
| Ttrue : Typ Γ .trueT type.boolean
| Tfalse : Typ Γ .falseT type.boolean
| TVar (x : Nat) (Γ : TCtx) (tp : type) :
  Γ.types x tp →
  Typ Γ (.Var x) tp
| TAbs (t : Term) (Γ : TCtx) (tp₁ tp₂ : type) :
  Typ (tp₁ :: Γ) t tp₂ →
  Typ Γ (t.Abs tp₁) (tp₁.arr tp₂)
| TApp (t₁ t₂ : Term) (Γ : TCtx) (tp₁ tp₂ : type) :
  Typ Γ t₁ (tp₁.arr tp₂) →
  Typ Γ t₂ tp₁ →
  Typ Γ (.App t₁ t₂) tp₂
| Tite (ct : Term) (t₁ t₂ : Term) (Γ : TCtx) (tp : type) :
  Typ Γ ct type.boolean →
  Typ Γ t₁ tp →
  Typ Γ t₂ tp →
  Typ Γ (.ite ct t₁ t₂) tp
| TZero (Γ : TCtx) : Typ Γ .Zero type.nat
| TSucc (t : Term) (Γ : TCtx) :
  Typ Γ t type.nat →
  Typ Γ (.Succ t) type.nat
| TPred (t : Term) (Γ : TCtx) :
  Typ Γ t type.nat →
  Typ Γ (.Pred t) type.nat
| TIsZero (t : Term) (Γ : TCtx) :
  Typ Γ t type.nat →
  Typ Γ (.IsZero t) type.boolean
| TRcd (tpt : List Term) (Γ : TCtx) (tpl₁ tpl₂ : SList Label) (tps : List type) :
  -- is there a way to do this better?
  tpt.length = tpl₁.elems.length →
  tpl₁.elems.Perm tpl₂.elems →
  tps.length = tpl₂.elems.length →
  (∀ i j, i < tpl₁.elems.length → j < tpl₂.elems.length → tpl₁.elems[i]! = tpl₂.elems[j]! →
    Typ Γ tpt[i]! tps[j]!) →
  Typ Γ (.Rcd tpt tpl₁) (.rcd tps tpl₂)
| TProj (t : Term) (l : Label) (Γ : TCtx)
  (tpl : SList Label) (tps : List type) (i : Nat) (tp : type) :
  -- we can do a step under index even if we have duplicates?
  Typ Γ t (.rcd tps tpl) →
  l = tpl.elems[i]! →
  tp = tps[i]! →
  i < tps.length →
  Typ Γ (.Proj t l) tp


def shift_up_from (c : Nat) : Term → Term
| .Zero => .Zero
| .trueT => .trueT
| .falseT => .falseT
| .Succ t => .Succ (shift_up_from c t)
| .Pred t => .Pred (shift_up_from c t)
| .IsZero t => .IsZero (shift_up_from c t)
| .Var x => if x < c then .Var x else .Var (x + 1)
| .Abs t tp => .Abs (shift_up_from (c + 1) t) tp
| .App t1 t2 => .App (shift_up_from c t1) (shift_up_from c t2)
| .ite ct t1 t2 => .ite (shift_up_from c ct) (shift_up_from c t1) (shift_up_from c t2)
| .Rcd tpt tpl => .Rcd (tpt.map (fun t => shift_up_from c t)) tpl
| .Proj t l => .Proj (shift_up_from c t) l

def shift_up (s : Term) : Term := shift_up_from 0 s

/-
Now this one is simply incorrect:
formally speaking, {"x" : nat, "y" : bool} and {"y" : bool, "x" : nat}
are two different types.

lemma TypDet (t : Term) (tp₁ tp₂ : type) (Γ : TCtx) :
  Typ Γ t tp₁ → Typ Γ t tp₂ → tp₁ = tp₂ := by
    intro h1 h2
    unhygienic induction h1 generalizing tp₂
    all_goals try
    { cases h2
      grind }
    { unhygienic cases h2
      simp
      sorry }
    unhygienic cases h2
    have lm := a_ih _ a_3
    simp at lm
    sorry
-/

def betar (k : Nat) (t s : Term) : Term :=
  match t with
  | .Var x => if x = k then s else if x < k then .Var x else .Var (x - 1)
  | .Abs t1 tp => (betar (k + 1) t1 (shift_up s)).Abs tp
  | .App t1 t2 => (betar k t1 s).App (betar k t2 s)
  | .trueT => .trueT
  | .falseT => .falseT
  | .ite ct t1 t2 => .ite (betar k ct s) (betar k t1 s) (betar k t2 s)
  | .Zero => .Zero
  | .Succ t => .Succ (betar k t s)
  | .Pred t => .Pred (betar k t s)
  | .IsZero t => .IsZero (betar k t s)
  | .Rcd tpt tpl => .Rcd (tpt.map (fun t => betar k t s)) tpl
  | .Proj t l => .Proj (betar k t s) l

abbrev subst (t s : Term) : Term := betar 0 t s

inductive Step : Term → Term → Prop
| AppL (t t' s : Term) :
  Step t t' →
  Step (t.App s) (t'.App s)
| AppR (t s' s : Term) :
  Value t →
  Step s s' →
  Step (t.App s) (t.App s')
| Beta (t s : Term) (tp : type) :
  Value s →
  Step ((t.Abs tp).App s) (subst t s)
| IteTrue (t1 t2 : Term) :
  Step (.ite .trueT t1 t2) t1
| IteFalse (t1 t2 : Term) :
  Step (.ite .falseT t1 t2) t2
| IteCond (ct ct' t1 t2 : Term) :
  Step ct ct' →
  Step (.ite ct t1 t2) (.ite ct' t1 t2)
| Succ (t t' : Term) :
  Step t t' →
  Step (.Succ t) (.Succ t')
| Pred (t t' : Term) :
  Step t t' →
  Step (.Pred t) (.Pred t')
| PredZero :
  Step (.Pred .Zero) .Zero
| PredSucc (t : Term) :
  NatValue t →
  Step (.Pred (.Succ t)) t
| IsZeroZero :
  Step (.IsZero .Zero) .trueT
| IsZeroSucc (t : Term) :
  NatValue t →
  Step (.IsZero (.Succ t)) .falseT
| IsZero (t t' : Term) :
  Step t t' →
  Step (.IsZero t) (.IsZero t')
| Rcd (tpt : List Term) (tpl : SList Label) (t : Term) (i : Nat) :
  Step tpt[i]! t →
  Step (.Rcd tpt tpl) (.Rcd (tpt.set i t) tpl)
| Proj (t t' : Term) (l : Label) :
  Step t t' →
  Step (.Proj t l) (.Proj t' l)
| ProjRcd (tpt : List Term) (tpl : SList Label) (k : Nat) :
  -- we can do a step under index even if we have duplicates?
  k < tpl.elems.length →
  k < tpt.length →
  Step (.Proj (.Rcd tpt tpl) tpl.elems[k]!) tpt[k]!

lemma beta_typ (tp : type) (S : type) :
  Γ₂ = Γ₁ ++ Γ → Typ Γ₂ s S → Typ (Γ₁ ++ tp :: Γ) (shift_up_from Γ₁.length s) S := by
  intro hs hs1
  induction hs1 generalizing Γ₁ Γ <;> try grind [Typ, shift_up_from]

lemma betar_preservation (t s : Term) (S T : type) (Γ Γ₁ : TCtx) :
  Γ₂ = Γ₁ ++ S :: Γ → Typ (Γ₁ ++ Γ) s S → Typ Γ₂ t T → Typ (Γ₁ ++ Γ) (betar Γ₁.length t s) T := by
    intro heq hs ht
    unhygienic induction ht generalizing Γ₁ S s
    iterate 2 { grind [Typ, betar] }
    { rw [betar]
      repeat' split <;> grind [Typ] }
    { rw [betar]
      apply Typ.TAbs
      have ih := a_ih (shift_up s) S (tp₁ :: Γ₁) (by grind) (by
        rw [shift_up]
        have typ_lm := beta_typ tp₁ S (Γ₁ := []) (Γ := Γ₁ ++ Γ) (by grind) hs
        grind)
      grind }
    all_goals { grind [betar, Typ] }

theorem preservation (t t' : Term) (tp : type) (Γ : TCtx) :
  Step t t' → Typ Γ t tp → Typ Γ t' tp := by
    intro hs ht
    unhygienic induction hs generalizing Γ tp
    iterate 2 { grind [Typ] }
    { unhygienic cases ht
      unhygienic cases a_1
      rename_i tp1
      have lm := betar_preservation t_1 s tp1 tp Γ [] (Γ₂ := tp1 :: Γ)
      grind }
    iterate 12 { grind [Typ] }
    grind [Typ]

lemma nat_value_from (ht : Typ Γ t type.nat) (hv : Value t) : NatValue t := by
  cases ht <;> cases hv <;> grind

lemma bool_value_from (ht : Typ Γ t type.boolean) (hv : Value t) :
  t = .trueT ∨ t = .falseT := by
  cases ht <;> cases hv
  all_goals (try contradiction)
  · grind
  · grind
theorem progress (t : Term) (td : Typ [] t T) :
  Value t ∨ ∃ t', Step t t' := by
  generalize h : [] = Γ at td
  induction td
  · grind [Value]
  · grind [Value]
  · grind
  · grind [Value]
  · rename_i ht _ ih1 ih2
    cases ih1 h
    · rename_i tp₁ tp₂ a hv
      generalize hp : tp₁.arr tp₂ = tp at ht
      cases ht <;> cases hv
      all_goals (try contradiction)
      cases ih2 h
      · rename_i t2 _ t _ _ _ _
        right
        exists subst t t2
        solve_by_elim
      · rename_i t tp _ _  hs
        have ⟨ t2', _ ⟩ := hs
        right
        exists (t.Abs tp).App t2'
        solve_by_elim
    · rename_i t2 _ _ _ _ hs
      have ⟨ t1', _ ⟩ := hs
      right
      exists (.App t1' t2)
      solve_by_elim
  · rename_i ihc iht ihe
    cases ihc h
    · rename_i t1 t2 _ _ _ _ _ _
      right
      cases bool_value_from (by assumption) (by assumption)
      · exists t1
        rename_i hc
        rw [hc]
        solve_by_elim
      · exists t2
        rename_i hc
        rw [hc]
        solve_by_elim
    · rename_i t1 t2 _ _ _ _ _ hs
      have ⟨ ct', _ ⟩ := hs
      right
      exists (.ite ct' t1 t2)
      solve_by_elim
  · grind [Value, NatValue]
  · rename_i ih
    cases ih h
    · cases nat_value_from (by assumption) (by assumption)
      · grind [Value, NatValue]
      · grind [Value, NatValue]
    · rename_i hs
      have ⟨ t', _ ⟩ := hs
      right
      exists (.Succ t')
      solve_by_elim
  · rename_i ih
    cases ih h
    · cases nat_value_from (by assumption) (by assumption)
      · right
        exists .Zero
        solve_by_elim
      · rename_i t _ _ _
        right
        exists t
        solve_by_elim
    · rename_i hs
      have ⟨ t', _ ⟩ := hs
      right
      exists (.Pred t')
      solve_by_elim
  · rename_i ht ih
    cases ih h
    · rename_i hv
      have nv := nat_value_from (by assumption) hv
      right
      cases nv
      · exists .trueT
        solve_by_elim
      · exists .falseT
        solve_by_elim
    · rename_i hs
      have ⟨ t', _ ⟩ := hs
      right
      exists (.IsZero t')
      solve_by_elim
  { rename_i tpt _ tpl₁ tpl₂ tps hl1 hl2 hls hd ih
    by_cases ha : ∀ i < tpt.length, Value tpt[i]!
    { left
      apply Value.RcdV
      solve_by_elim }
    right
    simp only [not_forall] at ha
    rcases ha with ⟨i, ht, htv⟩
    have ex2 : ∃ j < tpt.length, tpl₁.elems[i]! = tpl₂.elems[j]! := by
      have : tpt.length = tpl₂.elems.length := by
        grind [hl2.length_eq]
      rw [this]
      rcases SList.Perm.key_correspondence tpl₁ tpl₂ (by grind) ⟨i, by grind⟩ with ⟨j, hj⟩
      simp at hj
      grind
    rcases ex2 with ⟨j, hj⟩
    cases ih i j (by grind) (by grind [hl2.length_eq]) (by grind) h
    { grind }
    rename_i ht
    rcases ht with ⟨t1, ht1⟩
    exists Term.Rcd (tpt.set i t1) tpl₁
    solve_by_elim }
  right
  rename_i l _ tpl tps i tp tp₁ htp hk heq ih
  cases ih h <;> rename_i h1
  { cases h1
    iterate 4 grind [Typ, NatValue]
    rename_i tpt1 tpl1 hv
    cases tp₁
    have exi : ∃ j < tpt1.length, tpl1.elems[j]! = tpl.elems[i]! := by
      rename_i ht1 hsl ht2 ht
      have := SList.Perm.key_correspondence tpl tpl1 (by grind) ⟨i, by grind⟩
      grind
    rcases exi with ⟨j, hj, hq⟩
    exists tpt1[j]!
    rw [htp, ←hq]
    apply Step.ProjRcd tpt1 <;> grind }
  unhygienic cases h1
  exists w.Proj l
  apply Step.Proj
  apply h_1
end Subtyping
