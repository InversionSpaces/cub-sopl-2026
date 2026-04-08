import Mathlib.Tactic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.AList

namespace Subtyping

abbrev Label := String

mutual
inductive type
| boolean
| nat
| arr (tp : type) (ct : type)
| rcd (tp: rcd_type)
| top

inductive rcd_type
| rcd_nil
| rcd_cons (l : Label) (hd : type) (tl : rcd_type)
end

def rcd_type.proj (rcd : rcd_type) (l : Label) : Option type :=
match rcd with
| rcd_type.rcd_nil => none
| rcd_type.rcd_cons l' hd tl =>
  if l = l' then some hd else rcd_type.proj tl l

mutual
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
| Rcd (t : RcdTerm)
| Proj (t : Term) (l : Label)

inductive RcdTerm
| RcdNil
| RcdCons (l : Label) (hd : Term) (tl : RcdTerm)
end

inductive NatValue : Term → Prop
| ZeroV : NatValue .Zero
| SuccV (t : Term) : NatValue t → NatValue (.Succ t)

mutual
inductive RcdValue : RcdTerm → Prop
| RcdNilV : RcdValue RcdTerm.RcdNil
| RcdConsV (l : Label) (hd : Term) (tl : RcdTerm) :
  Value hd → RcdValue tl → RcdValue (RcdTerm.RcdCons l hd tl)

inductive Value : Term → Prop
| Abs (t : Term) (tp : type) : Value (t.Abs tp)
| trueV : Value .trueT
| falseV : Value .falseT
| NatV (t : Term) : NatValue t → Value t
| RcdV (t : RcdTerm) : RcdValue t → Value (Term.Rcd t)
end

abbrev TCtx := List type

@[simp, grind]
def TCtx.types (Γ : TCtx) (x : Nat) (tp : type) : Prop := Γ[x]? = tp

mutual
inductive RcdTyp : TCtx → RcdTerm → rcd_type → Prop
| RcdNil : RcdTyp Γ RcdTerm.RcdNil rcd_type.rcd_nil
| RcdCons (l : Label) (hd : Term) (tl : RcdTerm) (Γ : TCtx)
          (tp_hd : type) (tp_tl : rcd_type) :
  Typ Γ hd tp_hd → RcdTyp Γ tl tp_tl →
  RcdTyp Γ (RcdTerm.RcdCons l hd tl) (rcd_type.rcd_cons l tp_hd tp_tl)

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
| TRcd (t : RcdTerm) (Γ : TCtx) (tp : rcd_type) :
  RcdTyp Γ t tp → Typ Γ (.Rcd t) (type.rcd tp)
| TProj (t : Term) (l : Label) (Γ : TCtx) (tp : type) (rcd_tp : rcd_type) :
  Typ Γ t (type.rcd rcd_tp) →
  rcd_type.proj rcd_tp l = some tp →
  Typ Γ (.Proj t l) tp
end

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
| .Rcd t => .Rcd (shift_up_from_rcd c t)
| .Proj t l => .Proj (shift_up_from c t) l
where
  shift_up_from_rcd (c : Nat) : RcdTerm → RcdTerm
  | RcdTerm.RcdNil => RcdTerm.RcdNil
  | RcdTerm.RcdCons l hd tl =>
    RcdTerm.RcdCons l (shift_up_from c hd) (shift_up_from_rcd c tl)

def shift_up (s : Term) : Term := shift_up_from 0 s

mutual
lemma TypDet (t : Term) (tp₁ tp₂ : type) (Γ : TCtx) :
  Typ Γ t tp₁ → Typ Γ t tp₂ → tp₁ = tp₂ := by
    intro h1 h2
    cases t
    all_goals (
    try grind [Typ]
    try {
      cases h1
      cases h2
      have _ := TypDet (by assumption)
      grind
    })
    · rename_i t1 t2
      cases h1
      cases h2
      have _ := TypDet t2
      have _ := TypDet t1
      grind
    · rename_i t
      cases h1
      cases h2
      have _ := RcdTypDet t
      grind

lemma RcdTypDet (t : RcdTerm) (tp₁ tp₂ : rcd_type) (Γ : TCtx) :
  RcdTyp Γ t tp₁ → RcdTyp Γ t tp₂ → tp₁ = tp₂ := by
    intro h1 h2
    cases t <;> cases h1 <;> cases h2
    · rfl
    · rename_i th1 _ _ _ th2 _
      have _ := TypDet _ _ _ _ th1 th2
      have _ := RcdTypDet (by assumption)
      grind
end

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
  | .Rcd t => .Rcd (betar_rcd k t s)
  | .Proj t l => .Proj (betar k t s) l
where
  betar_rcd (k : Nat) (t : RcdTerm) (s : Term) : RcdTerm :=
  match t with
  | RcdTerm.RcdNil => RcdTerm.RcdNil
  | RcdTerm.RcdCons l hd tl =>
    RcdTerm.RcdCons l (betar k hd s) (betar_rcd k tl s)

abbrev subst (t s : Term) : Term := betar 0 t s

def RcdTerm.proj (t : RcdTerm) (l : Label) : Option Term :=
match t with
| RcdTerm.RcdNil => none
| RcdTerm.RcdCons l' hd tl =>
  if l = l' then some hd else tl.proj l

mutual
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
| Rcd (rl : RcdTerm) (rl' : RcdTerm) :
  RcdStep rl rl' →
  Step (.Rcd rl) (.Rcd rl')
| Proj (t t' : Term) (l : Label) :
  Step t t' →
  Step (.Proj t l) (.Proj t' l)
| ProjRcd (rl : RcdTerm) (l : Label) (v : Term) :
  RcdValue rl →
  rl.proj l = some v →
  Step (.Proj (.Rcd rl) l) v

inductive RcdStep : RcdTerm → RcdTerm → Prop
| RcdHere (l : Label) (hd hd' : Term) (tl : RcdTerm) :
  Step hd hd' →
  RcdStep (RcdTerm.RcdCons l hd tl) (RcdTerm.RcdCons l hd' tl)
| RcdThere (l : Label) (hd : Term) (tl tl' : RcdTerm) :
  Value hd → RcdStep tl tl' →
  RcdStep (RcdTerm.RcdCons l hd tl) (RcdTerm.RcdCons l hd tl')
end

lemma beta_typ (tp : type) (S : type) :
  Typ (Γ₁ ++ Γ) s S → Typ (Γ₁ ++ tp :: Γ) (shift_up_from Γ₁.length s) S := by
  intro hs
  cases s <;> try grind [Typ, shift_up_from]
  · cases hs
    rename_i htc ht1 ht2
    have _ := beta_typ tp _ ht1
    have _ := beta_typ tp _ ht2
    have _ := beta_typ tp _ htc
    grind [Typ, shift_up_from]
  · cases hs
    rename_i tp' _ ht
    have _ := beta_typ (Γ₁ := tp' :: Γ₁) tp _ ht
    grind [Typ, shift_up_from]
  · sorry
  · cases hs
    rename_i ht
    have _ := beta_typ tp _ ht
    grind [Typ, shift_up_from]
  · cases hs
    rename_i ht
    have _ := beta_typ tp _ ht
    grind [Typ, shift_up_from]
  · sorry
  · sorry
  · sorry

lemma betar_preservation (t s : Term) (S T : type) (Γ Γ₁ : TCtx) :
  Typ (Γ₁ ++ Γ) s S → Typ (Γ₁ ++ S :: Γ) t T → Typ (Γ₁ ++ Γ) (betar Γ₁.length t s) T := by
    intro hs ht
    unhygienic induction t generalizing Γ Γ₁ s S T
    all_goals (try grind [Typ, betar])
    · cases ht
      rw [betar]
      split
      · grind
      · split
        · grind [Typ]
        · grind [Typ]
    · cases ht
      rename_i tp2 ih
      rw [betar]
      apply Typ.TAbs
      apply t_ih (shift_up s) S tp2 Γ (tp :: Γ₁)
      · have lm := beta_typ tp (Γ₁ := []) (Γ := Γ₁ ++ Γ) (S := S) (s := s)
        grind [shift_up]
      · grind

theorem preservation (t t' : Term) (tp : type) (Γ : TCtx) :
  Step t t' → Typ Γ t tp → Typ Γ t' tp := by
    intro hs ht
    unhygienic induction hs generalizing Γ tp <;> try grind [Typ]
    unhygienic cases ht
    unhygienic cases a_1
    rename_i tp1
    have lm := betar_preservation t_1 s tp1 tp Γ []
    grind

lemma weakening (t : Term) (tp : type) (Γ Γ₁ : TCtx) :
  Typ Γ t tp → Typ (Γ ++ Γ₁) t tp := by
    intro ht
    induction ht <;> grind [Typ]

lemma nat_value_from (ht : Typ Γ t type.nat) (hv : Value t) : NatValue t := by
  cases ht <;> cases hv
  · contradiction
  · contradiction
  · contradiction
  · grind
  · grind
  · contradiction

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
    · rename_i hv
      cases ht <;> cases hv
      all_goals (try contradiction)
      cases ih2 h
      · rename_i t2 _ _ _ _ t _ _
        right
        exists subst t t2
        grind [Step]
      · rename_i tp _ _ t _ hs
        have ⟨ t2', _ ⟩ := hs
        right
        exists (t.Abs tp).App t2'
        grind [Step]
    · rename_i t2 _ _ _ _ hs
      have ⟨ t1', _ ⟩ := hs
      right
      exists (.App t1' t2)
      grind [Step]
  · rename_i ihc iht ihe
    cases ihc h
    · rename_i t1 t2 _ _ _ _ _ _
      right
      cases bool_value_from (by assumption) (by assumption)
      · exists t1
        grind [Step]
      · exists t2
        grind [Step]
    · rename_i t1 t2 _ _ _ _ _ hs
      have ⟨ ct', _ ⟩ := hs
      right
      exists (.ite ct' t1 t2)
      grind [Step]
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
      grind [Step]
  · rename_i ih
    cases ih h
    · cases nat_value_from (by assumption) (by assumption)
      · right
        exists .Zero
        grind [Step]
      · rename_i t _ _ _
        right
        exists t
        grind [Step]
    · rename_i hs
      have ⟨ t', _ ⟩ := hs
      right
      exists (.Pred t')
      grind [Step]
  · rename_i ht ih
    cases ih h
    · rename_i hv
      have nv := nat_value_from (by assumption) hv
      right
      cases nv
      · exists .trueT
        grind [Step]
      · exists .falseT
        grind [Step]
    · rename_i hs
      have ⟨ t', _ ⟩ := hs
      right
      exists (.IsZero t')
      grind [Step]

end Subtyping
