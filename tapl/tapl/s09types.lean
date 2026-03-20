import Mathlib.Tactic.Basic

inductive type
| unit
| boolean
| nat
| arr (tp : type) (ct : type)
| tuple (tp : List type)
deriving Inhabited

inductive Term
| unit : Term
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
| Tuple (tp : List Term)
| Proj (arg : Term) (n : Nat)
deriving Inhabited

inductive NatValue : Term → Prop
| ZeroV : NatValue .Zero
| SuccV (t : Term) : NatValue t → NatValue (.Succ t)

inductive Value : Term → Prop
| Abs (t : Term) (tp : type) : Value (t.Abs tp)
| trueV : Value .trueT
| falseV : Value .falseT
| unitV : Value .unit
| NatV (t : Term) : NatValue t → Value t
| TupleV (tp : List Term) :
  (∀ x ∈ tp, Value x) →
  Value (.Tuple tp)

abbrev TCtx := List type

@[simp, grind]
def TCtx.types (Γ : TCtx) (x : Nat) (tp : type) : Prop := Γ[x]? = tp

inductive Typ : TCtx → Term → type → Prop
| Tunit : Typ Γ .unit .unit
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
| TTuple (tup : List Term) (tupt : List type) :
  tup.length = tupt.length →
  (∀ i < tup.length, Typ Γ tup[i]! tupt[i]!) →
  Typ Γ (.Tuple tup) (.tuple tupt)
| TProj (tp : Term) (tupt : List type) (k : Nat) (tp₁ : type) :
  Typ Γ tp (.tuple tupt) →
  k < tupt.length →
  tp₁ = tupt[k]! →
  Typ Γ (.Proj tp k) tp₁

def shift_up_from (c : Nat) : Term → Term
| .unit => .unit
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
| .Tuple tp => .Tuple (tp.map (fun x => shift_up_from c x))
| .Proj arg n => .Proj (shift_up_from c arg) n

def shift_up (s : Term) : Term := shift_up_from 0 s

lemma TypDet (t : Term) (tp₁ tp₂ : type) (Γ : TCtx) :
  Typ Γ t tp₁ → Typ Γ t tp₂ → tp₁ = tp₂ := by
    intro h1 h2
    unhygienic induction h1 generalizing tp₂ <;> try grind [Typ]
    { cases h2
      simp only [type.tuple.injEq]
      ext
      grind }

def betar (k : Nat) (t s : Term) : Term :=
  match t with
  | .Var x => if x = k then s else if x < k then .Var x else .Var (x - 1)
  | .Abs t1 tp => (betar (k + 1) t1 (shift_up s)).Abs tp
  | .App t1 t2 => (betar k t1 s).App (betar k t2 s)
  | .trueT => .trueT
  | .falseT => .falseT
  | .unit => .unit
  | .ite ct t1 t2 => .ite (betar k ct s) (betar k t1 s) (betar k t2 s)
  | .Zero => .Zero
  | .Succ t => .Succ (betar k t s)
  | .Pred t => .Pred (betar k t s)
  | .IsZero t => .IsZero (betar k t s)
  | .Tuple tp => .Tuple (tp.map (fun t => betar k t s))
  | .Proj arg n => .Proj (betar k arg s) n

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
| ProjTuple (tp : List Term) :
  Step (.Proj (.Tuple tp) k) tp[k]!
| Proj (t t' : Term) :
  Step t t' →
  Step (.Proj t k) (.Proj t' k)
| Tuple (t' : Term) (k : Nat) (tp : List Term) :
  Step tp[k]! t' →
  Step (.Tuple tp) (.Tuple (tp.set k t'))


lemma beta_typ (tp : type) (S : type) :
  Γ₂ = Γ₁ ++ Γ → Typ Γ₂ s S → Typ (Γ₁ ++ tp :: Γ) (shift_up_from Γ₁.length s) S := by
  intro hs hs1
  unhygienic induction hs1 generalizing Γ₁ Γ <;> try grind [Typ, shift_up_from]

lemma betar_preservation (t s : Term) (S T : type) (Γ Γ₁ : TCtx) :
  Γ₂ = Γ₁ ++ S :: Γ → Typ (Γ₁ ++ Γ) s S → Typ Γ₂ t T → Typ (Γ₁ ++ Γ) (betar Γ₁.length t s) T := by
    intro heq hs ht
    unhygienic induction ht generalizing Γ₁ S s
    iterate 3 { grind [Typ, betar] }
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
    cases ht
    apply Typ.TTuple <;> grind

lemma weakening (t : Term) (tp : type) (Γ Γ₁ : TCtx) :
  Typ Γ t tp → Typ (Γ ++ Γ₁) t tp := by
    intro ht
    induction ht <;> grind [Typ]

lemma nat_value_from_gen (tp : type) (ht : Typ Γ t tp) (hv : Value t) :
  tp = .nat → NatValue t := by
  intro heq
  cases ht <;> cases hv <;> try grind [NatValue, Value]

lemma nat_value_from (ht : Typ Γ t .nat) (hv : Value t) :
  NatValue t := by
  grind [nat_value_from_gen]

lemma bool_value_from_gen (tp : type) (ht : Typ Γ t tp) (hv : Value t) :
  tp = .boolean → (t = .trueT ∨ t = .falseT) := by
  cases ht <;> cases hv <;> grind [NatValue]

lemma bool_value_from (ht : Typ Γ t type.boolean) (hv : Value t) :
  t = .trueT ∨ t = .falseT := by
  grind [bool_value_from_gen]

theorem progress (t : Term) (td : Typ [] t T) :
  Value t ∨ ∃ t', Step t t' := by
  generalize h : [] = Γ at td
  induction td
  · grind [Value]
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
        grind [Step]
      · rename_i t tp _ _  hs
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
  { rename_i tup tupt heq a a_ih
    by_cases ha : ∀ x ∈ tup, Value x
    { left
      apply Value.TupleV
      apply ha }
    simp only [Classical.not_forall] at ha
    rcases ha with ⟨x, hx, hvx⟩
    have ex : ∃ i < tup.length, tup[i]! = x := by
      clear a a_ih
      rw [List.mem_iff_getElem] at hx
      rcases hx with ⟨y, hy⟩
      exists y
      grind
    right
    rcases ex with ⟨i, hi⟩
    have : ∃ t', Step tup[i]! t' := by grind
    rcases this with ⟨tp', htp⟩
    exists (Term.Tuple (tup.set i tp'))
    apply Step.Tuple
    apply htp }
  right
  rename_i k tp₁ htp hk heq ih
  cases ih h <;> rename_i h1
  { cases h1 <;> (rename_i tp t'; cases htp) <;> try grind [NatValue]
    exists tp[k]!
    apply Step.ProjTuple }
  unhygienic cases h1
  exists w.Proj k
  apply Step.Proj
  apply h_1
