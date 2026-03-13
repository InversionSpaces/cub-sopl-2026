import Mathlib.Tactic.Basic

inductive type
| boolean
| arr (tp : type) (ct : type)

inductive Term
| trueT : Term
| falseT : Term
| ite (ct : Term) (t₁ : Term) (t₂ : Term) : Term
| Var (x : Nat)
| Abs (t : Term) (tp : type)
| App (t₁ : Term) (t₂ : Term)

abbrev TCtx := List type

@[simp, grind]
def TCtx.types (Γ : TCtx) (x : Nat) (tp : type) : Prop := Γ[x]? = tp

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

def shift_up_from (c : Nat) : Term → Term
| .Var x => if x < c then .Var x else .Var (x + 1)
| .Abs t tp => .Abs (shift_up_from (c + 1) t) tp
| .App t1 t2 => .App (shift_up_from c t1) (shift_up_from c t2)
| .trueT => .trueT
| .falseT => .falseT
| .ite ct t1 t2 => .ite (shift_up_from c ct) (shift_up_from c t1) (shift_up_from c t2)

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
  | .trueT => .trueT
  | .falseT => .falseT
  | .ite ct t1 t2 => .ite (betar k ct s) (betar k t1 s) (betar k t2 s)

abbrev subst (t s : Term) : Term := betar 0 t s

inductive Step : Term → Term → Prop
| Abs (t t' : Term) (tp : type) :
  Step t t' →
  Step (t.Abs tp) (t'.Abs tp)
| AppL (t t' s : Term) :
  Step t t' →
  Step (t.App s) (t'.App s)
| AppR (t s' s : Term) :
  Step s s' →
  Step (t.App s) (t.App s')
| Beta (t s : Term) (tp : type) :
  Step ((t.Abs tp).App s) (subst t s)
| IteTrue (t1 t2 : Term) :
  Step (.ite .trueT t1 t2) t1
| IteFalse (t1 t2 : Term) :
  Step (.ite .falseT t1 t2) t2
| IteCond (ct ct' t1 t2 : Term) :
  Step ct ct' →
  Step (.ite ct t1 t2) (.ite ct' t1 t2)
| IteThen (ct t1 t1' t2 : Term) :
  Step t1 t1' →
  Step (.ite ct t1 t2) (.ite ct t1' t2)
| IteElse (ct t2 t2' t1 : Term) :
  Step t2 t2' →
  Step (.ite ct t1 t2) (.ite ct t1 t2')

lemma beta_typ (tp : type) (S : type) :
  Typ (Γ₁ ++ Γ) s S → Typ (Γ₁ ++ tp :: Γ) (shift_up_from Γ₁.length s) S := by
  intro hs
  unhygienic induction s generalizing Γ₁ S <;> grind [Typ, shift_up_from]

lemma betar_preservation (t s : Term) (S T : type) (Γ Γ₁ : TCtx) :
  Typ (Γ₁ ++ Γ) s S → Typ (Γ₁ ++ S :: Γ) t T → Typ (Γ₁ ++ Γ) (betar Γ₁.length t s) T := by
    intro hs ht
    unhygienic induction t generalizing Γ Γ₁ s S T
    { grind [betar, Typ] }
    { grind [betar, Typ] }
    { grind [betar, Typ] }
    { rw [betar]
      unhygienic cases ht
      grind [Typ] }
    { unhygienic cases ht
      rw [betar]
      apply Typ.TAbs
      apply t_ih (shift_up s) S tp₂ Γ (tp :: Γ₁)
      { have lm := beta_typ tp (Γ₁ := []) (Γ := Γ₁ ++ Γ) (S := S) (s := s)
        grind [shift_up] }
      grind }
    rw [betar]
    grind [Typ]

theorem preservation (t t' : Term) (tp : type) (Γ : TCtx) :
  Step t t' → Typ Γ t tp → Typ Γ t' tp := by
    intro hs ht
    unhygienic induction hs generalizing Γ tp <;> try grind [Typ]
    unhygienic cases ht
    unhygienic cases a
    rename_i tp1
    have lm := betar_preservation t_1 s tp1 tp Γ []
    grind

lemma weakening (t : Term) (tp : type) (Γ Γ₁ : TCtx) :
  Typ Γ t tp → Typ (Γ ++ Γ₁) t tp := by
    intro ht
    induction ht <;> grind [Typ]

mutual
inductive NHead : Term → Prop where
| var {n} : NHead (.Var n)
| ite {ct t e} : NHead ct → NF t → NF e → NHead (.ite ct t e)
| app {t s} : NHead t → NF s → NHead (.App t s)

inductive NF : Term → Prop where
| abs {t tp} : NF t → NF (t.Abs tp)
| trueNF : NF .trueT
| falseNF : NF .falseT
| nhead  {t} : NHead t → NF t
end

theorem progress (t : Term) (td : Typ Γ t T) :
  NF t ∨ ∃ t', Step t t' := by
  induction td
  · grind [NF]
  · grind [NF]
  · grind [NF, NHead]
  · rename_i ih
    cases ih
    · grind [NF, NHead]
    · rename_i tp _ _ h
      have ⟨ t', _ ⟩ := h
      right
      exists t'.Abs tp
      grind [Step]
  · rename_i ih1 ih2
    cases ih1 <;> cases ih2
    · rename_i h1 h2
      cases h1
      · rename_i t₂ _ _ _ _ t' tp _ _
        right
        exists (subst t' t₂)
        grind [Step]
      · sorry
      · sorry
      · grind [NF, NHead]
    · rename_i t₁ t₂ _ _ _ _ _ _ h
      have ⟨ t', _ ⟩ := h
      right
      exists t₁.App t'
      grind [Step]
    · rename_i t₁ t₂ _ _ _ _ _ h _
      have ⟨ t', _ ⟩ := h
      right
      exists t'.App t₂
      grind [Step]
    · rename_i t₁ t₂ _ _ _ _ _ h _
      have ⟨ t', _ ⟩ := h
      right
      exists t'.App t₂
      grind [Step]
  · sorry
