import Mathlib.Tactic.Basic
import Batteries.Tactic.Init

namespace Refs
inductive type
| unit
| boolean
| nat
| arr (tp : type) (ct : type)
| ref (tp : type)

inductive Term
| UnitT : Term
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
| Ref (t : Term)
| Deref (t : Term)
| Assign (t₁ : Term) (t₂ : Term)
| Loc (l : Nat)

inductive NatValue : Term → Prop
| ZeroV : NatValue .Zero
| SuccV (t : Term) : NatValue t → NatValue (.Succ t)

inductive Value : Term → Prop
| Abs (t : Term) (tp : type) : Value (t.Abs tp)
| trueV : Value .trueT
| falseV : Value .falseT
| NatV (t : Term) : NatValue t → Value t
| LocV (l : Nat) : Value (.Loc l)
| UnitV : Value .UnitT

abbrev TCtx := List type
abbrev STCtx := List type

@[simp, grind]
def TCtx.types (Γ : TCtx) (x : Nat) (tp : type) : Prop := Γ[x]? = tp

@[simp, grind]
def STCtx.types (S : STCtx) (l : Nat) (tp : type) : Prop := S[l]? = tp

inductive Typ : TCtx → STCtx → Term → type → Prop
| Ttrue : Typ Γ C .trueT type.boolean
| Tfalse : Typ Γ C .falseT type.boolean
| TVar (x : Nat) (Γ : TCtx) (C : STCtx) (tp : type) :
  Γ.types x tp →
  Typ Γ C (.Var x) tp
| TAbs (t : Term) (Γ : TCtx) (C : STCtx) (tp₁ tp₂ : type) :
  Typ (tp₁ :: Γ) C t tp₂ →
  Typ Γ C (t.Abs tp₁) (tp₁.arr tp₂)
| TApp (t₁ t₂ : Term) (Γ : TCtx) (C : STCtx) (tp₁ tp₂ : type) :
  Typ Γ C t₁ (tp₁.arr tp₂) →
  Typ Γ C t₂ tp₁ →
  Typ Γ C (.App t₁ t₂) tp₂
| Tite (ct : Term) (t₁ t₂ : Term) (Γ : TCtx) (C : STCtx) (tp : type) :
  Typ Γ C ct type.boolean →
  Typ Γ C t₁ tp →
  Typ Γ C t₂ tp →
  Typ Γ C (.ite ct t₁ t₂) tp
| TZero (Γ : TCtx) : Typ Γ C .Zero type.nat
| TSucc (t : Term) (Γ : TCtx) (C : STCtx) :
  Typ Γ C t type.nat →
  Typ Γ C (.Succ t) type.nat
| TPred (t : Term) (Γ : TCtx) (C : STCtx) :
  Typ Γ C t type.nat →
  Typ Γ C (.Pred t) type.nat
| TIsZero (t : Term) (Γ : TCtx) (C : STCtx) :
  Typ Γ C t type.nat →
  Typ Γ C (.IsZero t) type.boolean
| TUnit (Γ : TCtx) : Typ Γ C .UnitT type.unit
| TRef (t : Term) (Γ : TCtx) (C : STCtx) (tp : type) :
  Typ Γ C t tp →
  Typ Γ C (.Ref t) (type.ref tp)
| TDeref (t : Term) (Γ : TCtx) (C : STCtx) (tp : type) :
  Typ Γ C t (type.ref tp) →
  Typ Γ C (.Deref t) tp
| TAssign (t₁ t₂ : Term) (Γ : TCtx) (C : STCtx) (tp : type) :
  Typ Γ C t₁ (type.ref tp) →
  Typ Γ C t₂ tp →
  Typ Γ C (.Assign t₁ t₂) type.unit
| TLoc (l : Nat) (Γ : TCtx) (C : STCtx) (tp : type) :
  C.types l tp →
  Typ Γ C (.Loc l) (type.ref tp)

def shift_up_from (c : Nat) : Term → Term
| .UnitT => .UnitT
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
| .Ref t => .Ref (shift_up_from c t)
| .Deref t => .Deref (shift_up_from c t)
| .Assign t1 t2 => .Assign (shift_up_from c t1) (shift_up_from c t2)
| .Loc l => .Loc l

def shift_up (s : Term) : Term := shift_up_from 0 s

lemma TypDet (t : Term) (tp₁ tp₂ : type) (Γ : TCtx) (S : STCtx) :
  Typ Γ S t tp₁ → Typ Γ S t tp₂ → tp₁ = tp₂ := by
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
  | .Zero => .Zero
  | .Succ t => .Succ (betar k t s)
  | .Pred t => .Pred (betar k t s)
  | .IsZero t => .IsZero (betar k t s)
  | .UnitT => .UnitT
  | .Ref t => .Ref (betar k t s)
  | .Deref t => .Deref (betar k t s)
  | .Assign t1 t2 => .Assign (betar k t1 s) (betar k t2 s)
  | .Loc l => .Loc l

abbrev subst (t s : Term) : Term := betar 0 t s

abbrev ValueTerm := { x : Term // Value x }
abbrev Store := List ValueTerm

@[simp, grind]
def Store.contains (μ : Store) (l : Nat) : Prop := μ.length > l

@[simp, grind]
def Store.stores (μ : Store) (l : Nat) (v : ValueTerm) : Prop := μ[l]? = some v

inductive Step : Term × Store → Term × Store → Prop
| AppL (t t' s : Term) :
  Step (t, μ) (t', μ') →
  Step (t.App s, μ) (t'.App s, μ')
| AppR (t s' s : Term) :
  Value t →
  Step (s, μ) (s', μ') →
  Step (t.App s, μ) (t.App s', μ')
| Beta (t s : Term) (tp : type) :
  Value s →
  Step ((t.Abs tp).App s, μ) (subst t s, μ)
| IteTrue (t1 t2 : Term) :
  Step (.ite .trueT t1 t2, μ) (t1, μ)
| IteFalse (t1 t2 : Term) :
  Step (.ite .falseT t1 t2, μ) (t2, μ)
| IteCond (ct ct' t1 t2 : Term) :
  Step (ct, μ) (ct', μ') →
  Step (.ite ct t1 t2, μ) (.ite ct' t1 t2, μ')
| Succ (t t' : Term) :
  Step (t, μ) (t', μ') →
  Step (.Succ t, μ) (.Succ t', μ')
| Pred (t t' : Term) :
  Step (t, μ) (t', μ') →
  Step (.Pred t, μ) (.Pred t', μ')
| PredZero :
  Step (.Pred .Zero, μ) (.Zero, μ)
| PredSucc (t : Term) :
  NatValue t →
  Step (.Pred (.Succ t), μ) (t, μ)
| IsZeroZero :
  Step (.IsZero .Zero, μ) (.trueT, μ)
| IsZeroSucc (t : Term) :
  NatValue t →
  Step (.IsZero (.Succ t), μ) (.falseT, μ)
| IsZero (t t' : Term) :
  Step (t, μ) (t', μ') →
  Step (.IsZero t, μ) (.IsZero t', μ')
| Ref (t t' : Term) :
  Step (t, μ) (t', μ') →
  Step (.Ref t, μ) (.Ref t', μ')
| RefVal (v : ValueTerm) :
  Step (.Ref v.val, μ) (.Loc μ.length, μ ++ [v])
| Deref (t t' : Term) :
  Step (t, μ) (t', μ') →
  Step (.Deref t, μ) (.Deref t', μ')
| DerefLoc (l : Nat) (v : ValueTerm) :
  μ.stores l v →
  Step (.Deref (.Loc l), μ) (v.val, μ)
| AssignL (t₁ t₁' t₂ : Term) :
  Step (t₁, μ) (t₁', μ') →
  Step (.Assign t₁ t₂, μ) (.Assign t₁' t₂, μ')
| AssignR (t₁ t₂ t₂' : Term) :
  Value t₁ →
  Step (t₂, μ) (t₂', μ') →
  Step (.Assign t₁ t₂, μ) (.Assign t₁ t₂', μ')
| Assign (l : Nat) (t : Term) (μ : Store) :
  (hv : Value t) → μ.contains l →
  Step (.Assign (.Loc l) t, μ) (.UnitT, μ.set l ⟨ t, hv ⟩)

lemma beta_typ (tp S : type) (s : Term) :
  Typ (Γ₁ ++ Γ) C s S → Typ (Γ₁ ++ tp :: Γ) C (shift_up_from Γ₁.length s) S := by
  intro hs
  unhygienic induction s generalizing Γ₁ S <;> grind [Typ, shift_up_from]

lemma betar_preservation (t s : Term) (S T : type) (Γ Γ₁ : TCtx) :
  Typ (Γ₁ ++ Γ) C s S → Typ (Γ₁ ++ S :: Γ) C t T → Typ (Γ₁ ++ Γ) C (betar Γ₁.length t s) T := by
    intro hs ht
    unhygienic induction t generalizing Γ Γ₁ s S T
    case Var =>
      cases ht
      rw [betar]
      split
      · grind
      · split
        · grind [Typ]
        · grind [Typ]
    case Abs =>
      cases ht
      rename_i tp2 ih
      rw [betar]
      apply Typ.TAbs
      apply t_ih (shift_up s) S tp2 Γ (tp :: Γ₁)
      · have lm := beta_typ (C := C) tp (Γ₁ := []) (Γ := Γ₁ ++ Γ) (S := S) (s := s)
        grind [shift_up]
      · grind
    all_goals (try grind [Typ, betar])

structure STyp (Γ : TCtx) (C : STCtx) (μ : Store) : Prop where
  hl : C.length = μ.length
  ht : ∀ l tp, (h : C.types l tp) → Typ Γ C (μ.get ⟨ l, by grind ⟩) tp

@[simp, grind]
def Types (Γ : TCtx) (S : STCtx) (s : Term × Store) (tp : type) : Prop :=
  match s with
  | (t, μ) => Typ Γ S t tp ∧ STyp Γ S μ

@[simp]
lemma stctx_type_weakening :
  Typ Γ C t T → C <+: C' → Typ Γ C' t T := by
  intro ht hpref
  cases hpref
  induction ht <;> grind [Typ]

lemma styp_set (v : ValueTerm) :
  STyp Γ C μ → C.types l T → Typ Γ C v T →
  STyp Γ C (μ.set l v) := by grind [STyp]

set_option maxHeartbeats 1000000 in
-- most of the goals are similar, can be automated with increased limits
theorem preservation (Γ : TCtx) (C : STCtx) (tp : type) :
  Step s s' → Types Γ C s tp →
  ∃ C', Types Γ C' s' tp ∧ C <+: C' := by
    intro hs ht
    induction hs generalizing tp
    case RefVal =>
      rcases ht with ⟨ typ, styp ⟩
      cases typ
      rcases styp with ⟨ hl, htp ⟩
      rename_i μ _ tp _
      exists C ++ [tp]
      all_goals (repeat constructor <;> try grind)
      intro l tp' _
      by_cases hl' : l = μ.length
      · grind [stctx_type_weakening]
      · have _ := htp l tp' (by grind)
        grind [stctx_type_weakening]
    case DerefLoc =>
      rcases ht with ⟨ typ, styp ⟩
      cases typ
      rcases styp with ⟨ hl, htp ⟩
      rename_i μ _ _ tp typ
      cases typ
      exists C
      constructor
      · constructor
        · grind
        · constructor <;> assumption
      · grind
    all_goals try
    { rcases ht with ⟨ typ, styp ⟩
      cases typ
      exists C
      grind [Typ, styp_set] }
    all_goals try
    { rename_i ih
      rcases ht with ⟨ typ, styp ⟩
      cases typ
      rcases ih _ ⟨ by assumption, by assumption ⟩ with ⟨ C', ⟨ _, _ ⟩, hpref ⟩
      exists C'
      repeat constructor <;> try assumption
      all_goals (
        apply stctx_type_weakening
        repeat assumption) }
    { rename_i t s tp _
      rcases ht with ⟨ typ, styp ⟩
      cases typ
      rename_i ta
      cases ta
      rename_i stp _ _ _
      exists C
      have _ := betar_preservation (C := C) t s stp tp Γ []
      grind }

lemma nat_value_from (ht : Typ Γ C t type.nat) (hv : Value t) : NatValue t := by
  cases ht <;> cases hv <;> grind

theorem progress (t : Term) (s : Store) (tp : type) (ht : Types [] C ⟨t, s⟩ tp) :
  Value t ∨ ∃ t', Step ⟨t, s⟩ t' := by
  rcases ht with ⟨ht, hst⟩
  rcases hst with ⟨hl, hg⟩
  generalize h : [] = Γ at ht
  unhygienic induction ht
  { grind [Value] }
  { grind [Value] }
  { grind [Value] }
  { grind [Value] }
  { right
    unhygienic cases a_ih (by grind) (by grind) h
    { unhygienic cases a_ih_1 (by grind) (by grind) h
      { cases a <;> try grind [Value, NatValue]
        eapply Exists.intro
        apply Step.Beta <;> solve_by_elim }
      cases h_2
      eapply Exists.intro
      apply Step.AppR <;> solve_by_elim }
    cases h_1
    eapply Exists.intro
    apply Step.AppL <;> solve_by_elim }
  { right
    unhygienic cases a_ih (by grind) (by grind) h
    { cases h_1
      { cases a }
      { eapply Exists.intro
        apply Step.IteTrue }
      { eapply Exists.intro
        apply Step.IteFalse }
      { cases a <;> grind [NatValue] }
      { cases a }
      cases a }
    rcases h_1
    eapply Exists.intro
    apply Step.IteCond
    solve_by_elim }
  { grind [Value, NatValue] }
  { unhygienic cases a_ih (by grind) (by grind) h
    { have val_lemma := nat_value_from a h_1
      grind [Value, NatValue] }
    right
    cases h_1
    eapply Exists.intro
    apply Step.Succ
    solve_by_elim }
  { right
    unhygienic cases a_ih (by grind) (by grind) h
    { have val_lemma := nat_value_from a h_1
      cases val_lemma
      { eapply Exists.intro
        apply Step.PredZero }
      eapply Exists.intro
      apply Step.PredSucc <;> grind }
    cases h_1
    eapply Exists.intro
    apply Step.Pred
    solve_by_elim }
  { right
    unhygienic cases a_ih (by grind) (by grind) h
    { have val_lemma := nat_value_from a h_1
      cases val_lemma
      { eapply Exists.intro
        apply Step.IsZeroZero }
      eapply Exists.intro
      apply Step.IsZeroSucc <;> grind }
    cases h_1
    eapply Exists.intro
    apply Step.IsZero
    solve_by_elim }
  { grind [Value] }
  { unhygienic cases a_ih (by grind) (by grind) h
    {
      right
      let v : ValueTerm := ⟨ t_1, by assumption ⟩
      exists ⟨.Loc s.length, s ++ [v]⟩
      -- WTF, why do I have to do this?
      have h : t_1.Ref = v.val.Ref := by rfl
      rw [h]
      apply Step.RefVal
    }
    right
    cases h_1
    eapply Exists.intro
    apply Step.Ref
    solve_by_elim }
  { right
    unhygienic cases a_ih (by grind) (by grind) h
    { unhygienic cases a <;> try grind [Value, NatValue]
      exists ⟨ s.get ⟨ l, by grind ⟩ , s ⟩
      grind [Step] }
    cases h_1
    eapply Exists.intro
    apply Step.Deref
    solve_by_elim }
  { right
    unhygienic cases a_ih (by grind) (by grind) h
    { cases a <;> try grind [Value, NatValue]
      unhygienic cases a_ih_1 (by grind) (by grind) h
      { eapply Exists.intro
        apply Step.Assign <;> grind }
      cases h_2
      eapply Exists.intro
      apply Step.AssignR <;> solve_by_elim }
    cases h_1
    eapply Exists.intro
    apply Step.AssignL
    solve_by_elim }
  grind [Value]
end Refs
