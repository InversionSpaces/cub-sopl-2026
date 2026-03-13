import Mathlib.Tactic.Basic

inductive type
| base
| arr (tp : type) (ct : type)

inductive Term
| Var (x : Nat)
| Abs (t : Term) (tp : type)
| App (t₁ : Term) (t₂ : Term)

inductive Typ : List type → Term → type → Prop
| TVar (x : Nat) (Γ : List type) (tp : type) :
  x < Γ.length →
  Γ[x]? = tp →
  Typ Γ (.Var x) tp
| TAbs (t : Term) (Γ : List type) (tp₁ tp₂ : type) :
  Typ (tp₁ :: Γ) t tp₂ →
  Typ Γ (t.Abs tp₁) (tp₁.arr tp₂)
| TApp (t₁ t₂ : Term) (Γ : List type) (tp₁ tp₂ : type) :
  Typ Γ t₁ (tp₁.arr tp₂) →
  Typ Γ t₂ tp₁ →
  Typ Γ (.App t₁ t₂) tp₂

def shift_up_from (c : Nat) : Term → Term
| .Var x => if x < c then .Var x else .Var (x + 1)
| .Abs t tp => .Abs (shift_up_from (c + 1) t) tp
| .App t1 t2 => .App (shift_up_from c t1) (shift_up_from c t2)

def shift_up (s : Term) : Term := shift_up_from 0 s

lemma TypDet (t : Term) (tp₁ tp₂ : type) (Γ : List type) :
  Typ Γ t tp₁ → Typ Γ t tp₂ → tp₁ = tp₂ := by
    intro h1 h2
    unhygienic induction t generalizing Γ tp₁ tp₂ <;> grind [Typ]

def betar (k : Nat) (t s : Term) : Term :=
  match t with
  | .Var x => if x = k then s else if x < k then .Var x else .Var (x - 1)
  | .Abs t1 tp => (betar (k + 1) t1 (shift_up s)).Abs tp
  | .App t1 t2 => (betar k t1 s).App (betar k t2 s)

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
  Step ((t.Abs tp).App s) (betar 0 t s)

lemma beta_typ (tp : type) (S : type) :
  Typ (Γ₁ ++ Γ) s S → Typ (Γ₁ ++ tp :: Γ) (shift_up_from Γ₁.length s) S := by
  intro hs
  unhygienic induction s generalizing Γ₁ S <;> grind [Typ, shift_up_from]

lemma betar_preservation (t s : Term) (S T : type) (Γ Γ₁ : List type) :
  Typ (Γ₁ ++ Γ) s S → Typ (Γ₁ ++ S :: Γ) t T → Typ (Γ₁ ++ Γ) (betar Γ₁.length t s) T := by
    intro hs ht
    unhygienic induction t generalizing Γ Γ₁ s S T
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

theorem preservation (t t' : Term) (tp : type) (Γ : List type) :
  Step t t' → Typ Γ t tp → Typ Γ t' tp := by
    intro hs ht
    unhygienic induction hs generalizing Γ tp <;> try grind [Typ]
    unhygienic cases ht
    unhygienic cases a
    rename_i tp1
    have lm := betar_preservation t_1 s tp1 tp Γ []
    grind

lemma weakening (t : Term) (tp : type) (Γ Γ₁ : List type) :
  Typ Γ t tp → Typ (Γ ++ Γ₁) t tp := by
    intro ht
    induction ht <;> grind [Typ]

mutual
inductive NHead : Term → Prop where
| var {n} : NHead (.Var n)
| app {t s} : NHead t → NF s → NHead (.App t s)

inductive NF : Term → Prop where
| abs {t tp} : NF t → NF (t.Abs tp)
| ne  {t} : NHead t → NF t
end

theorem progress (t : Term) (td : Typ Γ t T) :
  NF t ∨ ∃ t', Step t t' := by
  induction td
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
        exists (betar 0 t' t₂)
        grind [Step]
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
