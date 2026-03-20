import Mathlib.Tactic.Basic

inductive type
| boolean
| nat
| arr (tp : type) (ct : type)
| list (tp : type)

inductive Term
| TrueT : Term
| FalseT : Term
| Ite (ct : Term) (t₁ : Term) (t₂ : Term) : Term
| Var (x : Nat)
| Abs (t : Term) (tp : type)
| App (t₁ : Term) (t₂ : Term)
| Zero
| Succ (t : Term)
| Pred (t : Term)
| IsZero (t : Term)
| Nil (tp : type)
| Cons (tp: type) (h : Term) (t : Term)
| IsNil (tp: type) (t : Term)
| Fold (a l f : Term)

inductive NatValue : Term → Prop
| ZeroV : NatValue .Zero
| SuccV (t : Term) : NatValue t → NatValue (.Succ t)

inductive Value : Term → Prop
| Abs (t : Term) (tp : type) : Value (t.Abs tp)
| trueV : Value .TrueT
| falseV : Value .FalseT
| NatV (t : Term) : NatValue t → Value t
| NilV (tp : type) : Value (.Nil tp)
| ConsV (tp : type) (h t : Term) : Value h → Value t → Value (.Cons tp h t)

abbrev TCtx := List type

@[simp, grind]
def TCtx.types (Γ : TCtx) (x : Nat) (tp : type) : Prop := Γ[x]? = tp

inductive Typ : TCtx → Term → type → Prop
| Ttrue : Typ Γ .TrueT type.boolean
| Tfalse : Typ Γ .FalseT type.boolean
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
  Typ Γ (.Ite ct t₁ t₂) tp
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
| TNil (tp : type) (Γ : TCtx) :
  Typ Γ (.Nil tp) (type.list tp)
| TCons (tp : type) (h t : Term) (Γ : TCtx) :
  Typ Γ h tp → Typ Γ t (type.list tp) →
  Typ Γ (.Cons tp h t) (type.list tp)
| TIsNil (tp : type) (t : Term) (Γ : TCtx) :
  Typ Γ t (type.list tp) →
  Typ Γ (.IsNil tp t) type.boolean
| TFold (aT lT : type) (a l f : Term) (Γ : TCtx) :
  Typ Γ a aT → Typ Γ l (type.list lT) →
  Typ Γ f (type.arr lT (type.arr aT aT)) →
  Typ Γ (.Fold a l f) aT

def shift_up_from (c : Nat) : Term → Term
| .Zero => .Zero
| .TrueT => .TrueT
| .FalseT => .FalseT
| .Succ t => .Succ (shift_up_from c t)
| .Pred t => .Pred (shift_up_from c t)
| .IsZero t => .IsZero (shift_up_from c t)
| .Var x => if x < c then .Var x else .Var (x + 1)
| .Abs t tp => .Abs (shift_up_from (c + 1) t) tp
| .App t1 t2 => .App (shift_up_from c t1) (shift_up_from c t2)
| .Ite ct t1 t2 => .Ite (shift_up_from c ct) (shift_up_from c t1) (shift_up_from c t2)
| .Nil tp => .Nil tp
| .Cons tp h t => .Cons tp (shift_up_from c h) (shift_up_from c t)
| .IsNil tp t => .IsNil tp (shift_up_from c t)
| .Fold a l f => .Fold (shift_up_from c a) (shift_up_from c l) (shift_up_from c f)

def shift_up (s : Term) : Term := shift_up_from 0 s

lemma TypDet (t : Term) (tp₁ tp₂ : type) (Γ : TCtx) :
  Typ Γ t tp₁ → Typ Γ t tp₂ → tp₁ = tp₂ := by
    intro h1 h2
    unhygienic induction t generalizing Γ tp₁ tp₂ <;> grind [Typ]

def betar (k : Nat) (t s : Term) : Term :=
  match t with
  | .Var x => if x = k then s else if x < k then .Var x else .Var (x - 1)
  | .Abs t1 tp => (betar (k + 1) t1 (shift_up s)).Abs tp
  | .App t1 t2 => (betar k t1 s).App (betar k t2 s)
  | .TrueT => .TrueT
  | .FalseT => .FalseT
  | .Ite ct t1 t2 => .Ite (betar k ct s) (betar k t1 s) (betar k t2 s)
  | .Zero => .Zero
  | .Succ t => .Succ (betar k t s)
  | .Pred t => .Pred (betar k t s)
  | .IsZero t => .IsZero (betar k t s)
  | .Nil tp => .Nil tp
  | .Cons tp h t => .Cons tp (betar k h s) (betar k t s)
  | .IsNil tp t => .IsNil tp (betar k t s)
  | .Fold a l f => .Fold (betar k a s) (betar k l s) (betar k f s)

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
  Step (.Ite .TrueT t1 t2) t1
| IteFalse (t1 t2 : Term) :
  Step (.Ite .FalseT t1 t2) t2
| IteCond (ct ct' t1 t2 : Term) :
  Step ct ct' →
  Step (.Ite ct t1 t2) (.Ite ct' t1 t2)
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
  Step (.IsZero .Zero) .TrueT
| IsZeroSucc (t : Term) :
  NatValue t →
  Step (.IsZero (.Succ t)) .FalseT
| IsZero (t t' : Term) :
  Step t t' →
  Step (.IsZero t) (.IsZero t')
| ConsH (tp : type) (h h' t : Term) :
  Step h h' →
  Step (.Cons tp h t) (.Cons tp h' t)
| ConsT (tp : type) (h t t' : Term) :
  Value h → Step t t' →
  Step (.Cons tp h t) (.Cons tp h t')
| IsNil (tp : type) (t t' : Term) :
  Step t t' →
  Step (.IsNil tp t) (.IsNil tp t')
| IsNilNil (tp : type) :
  Step (.IsNil tp (.Nil tp)) .TrueT
| IsNilCons (tp : type) (h t : Term) :
  Value h → Value t →
  Step (.IsNil tp (.Cons tp h t)) .FalseT
| FoldA (a a' l f : Term) :
  Step a a' →
  Step (.Fold a l f) (.Fold a' l f)
| FoldL (a l l' f : Term) :
  Value a → Step l l' →
  Step (.Fold a l f) (.Fold a l' f)
| FoldF (a l f f' : Term) :
  Value a → Value l → Step f f' →
  Step (.Fold a l f) (.Fold a l f')
| FoldNil (tp : type) (a f : Term) :
  Value a → Value f →
  Step (.Fold a (.Nil tp) f) a
| FoldCons (tp : type) (a h t f : Term) :
  Value a → Value f → Value h → Value t →
  Step (.Fold a (.Cons tp h t) f) (.App (.App f h) (.Fold a t f))

lemma beta_typ (tp : type) (S : type) :
  Typ (Γ₁ ++ Γ) s S → Typ (Γ₁ ++ tp :: Γ) (shift_up_from Γ₁.length s) S := by
  intro hs
  unhygienic induction s generalizing Γ₁ S <;> grind [Typ, shift_up_from]

lemma betar_preservation (t s : Term) (S T : type) (Γ Γ₁ : TCtx) :
  Typ (Γ₁ ++ Γ) s S → Typ (Γ₁ ++ S :: Γ) t T → Typ (Γ₁ ++ Γ) (betar Γ₁.length t s) T := by
    intro hs ht
    unhygienic induction t generalizing Γ Γ₁ s S T
    case Abs =>
      cases ht
      rename_i tp2 ih
      rw [betar]
      apply Typ.TAbs
      apply t_ih (shift_up s) S tp2 Γ (tp :: Γ₁)
      · have lm := beta_typ tp (Γ₁ := []) (Γ := Γ₁ ++ Γ) (S := S) (s := s)
        grind [shift_up]
      · grind
    case Var =>
      cases ht
      rw [betar]
      split
      · grind
      · split
        · grind [Typ]
        · grind [Typ]
    all_goals (grind [Typ, betar])

theorem preservation (t t' : Term) (tp : type) (Γ : TCtx) :
  Step t t' → Typ Γ t tp → Typ Γ t' tp := by
  intro hs ht
  induction hs generalizing Γ tp <;> try grind [Typ, Typ.TApp]
  case Beta =>
    cases ht
    rename_i ht'
    cases ht'
    rename_i t' s tps _ _ _
    have lm := betar_preservation t' s tps tp Γ []
    grind

lemma weakening (t : Term) (tp : type) (Γ Γ₁ : TCtx) :
  Typ Γ t tp → Typ (Γ ++ Γ₁) t tp := by
  intro ht
  induction ht <;> grind [Typ]

lemma nat_value_from (ht : Typ Γ t type.nat) (hv : Value t) : NatValue t := by
  cases ht <;> cases hv
  all_goals (grind)

lemma bool_value_from (ht : Typ Γ t type.boolean) (hv : Value t) :
  t = .TrueT ∨ t = .FalseT := by
  cases ht <;> cases hv
  all_goals (try contradiction)
  all_goals (grind)

lemma list_value_from {tp : type} (ht : Typ Γ t (type.list tp)) (hv : Value t) :
  t = .Nil tp ∨ ∃ h t', Value h ∧ Value t' ∧ t = .Cons tp h t' := by
  cases ht <;> cases hv
  all_goals (try contradiction)
  all_goals (grind)

theorem progress (t : Term) (td : Typ [] t T) :
  Value t ∨ ∃ t', Step t t' := by
  generalize h : [] = Γ at td
  induction td
  all_goals (try grind [Value])
  case TApp =>
    rename_i ht _ ih1 ih2
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
  case Tite =>
    rename_i ihc iht ihe
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
      exists (.Ite ct' t1 t2)
      grind [Step]
  · grind [Value, NatValue]
  case TSucc =>
    rename_i ih
    cases ih h
    · cases nat_value_from (by assumption) (by assumption)
      · grind [Value, NatValue]
      · grind [Value, NatValue]
    · rename_i hs
      have ⟨ t', _ ⟩ := hs
      right
      exists (.Succ t')
      grind [Step]
  case TPred =>
    rename_i ih
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
  case TIsZero =>
    rename_i ht ih
    cases ih h
    · rename_i hv
      have nv := nat_value_from (by assumption) hv
      right
      cases nv
      · exists .TrueT
        grind [Step]
      · exists .FalseT
        grind [Step]
    · rename_i hs
      have ⟨ t', _ ⟩ := hs
      right
      exists (.IsZero t')
      grind [Step]
  case TCons =>
    rename_i ihh iht
    cases ihh h
    · cases iht h
      · left
        grind [Value]
      · rename_i tp hd _ _ _ _ _ hs
        have ⟨ t', _ ⟩ := hs
        right
        exists .Cons tp hd t'
        grind [Step]
    · rename_i tp _ tl _ _ _ hs
      have ⟨ hd', _ ⟩ := hs
      right
      exists .Cons tp hd' tl
      grind [Step]
  case TIsNil =>
    rename_i typ ih
    cases ih h
    · rename_i hv
      cases list_value_from (by assumption) hv
      · rename_i hnil
        right
        rw [hnil]
        exists .TrueT
        grind [Step]
      · rename_i hs
        have ⟨ _, _, ⟨ _, _, htl ⟩ ⟩ := hs
        rw [htl]
        right
        exists .FalseT
        grind [Step]
    · rename_i tp _ _ hs
      have ⟨ t', _ ⟩ := hs
      right
      exists (.IsNil tp t')
      grind [Step]
  case TFold =>
    rename_i a l f _ _ _ _ iha ihl ihf
    cases iha h
    · rename_i hva
      cases ihl h
      · rename_i hvl
        cases ihf h
        · rename_i hvf
          cases list_value_from (by assumption) hvl
          · rename_i hnil
            right
            rw [hnil]
            exists a
            grind [Step]
          · rename_i hs
            have ⟨ hd, tl, ⟨ _, _, htl ⟩ ⟩ := hs
            rw [htl]
            right
            exists (.App (.App f hd) (.Fold a tl f))
            grind [Step]
        · rename_i hsf
          have ⟨ f', _ ⟩ := hsf
          right
          exists (.Fold a l f')
          grind [Step]
      · rename_i hsl
        have ⟨ l', _ ⟩ := hsl
        right
        exists (.Fold a l' f)
        grind [Step]
    · rename_i hsa
      have ⟨ a', _ ⟩ := hsa
      right
      exists (.Fold a' l f)
      grind [Step]
