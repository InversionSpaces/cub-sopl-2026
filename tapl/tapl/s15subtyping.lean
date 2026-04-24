import Mathlib.Tactic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.AList
import Mathlib.Data.List.Induction

namespace Subtyping

abbrev Label := String

@[grind]
structure SList (α : Type*) [DecidableEq α] where
  elems : List α
  nodup : elems.Nodup

@[simp, grind]
def SList.length [DecidableEq α] (s : SList α) : Nat := s.elems.length

def SList.IsPrefix [DecidableEq α] (s t : SList α) : Prop := s.elems.IsPrefix t.elems

def SList.Perm [DecidableEq α] (s t : SList α) : Prop := s.elems.Perm t.elems

def SList.Subperm [DecidableEq α] (s t : SList α) : Prop := s.elems.Subperm t.elems

@[grind]
def SList.assoc [DecidableEq α]
  (s : SList α) (a : α) (e : List β) (b : β) : Prop :=
  ∃ i < s.length, s.elems[i]? = some a ∧ e[i]? = some b

instance (α : Type*) [DecidableEq α] : Inhabited (SList α) where
  default := ⟨[], by simp⟩

@[simp, grind]
def forall_valid {α : Type} [Inhabited α] (ls : List α) (P : α → Prop) : Prop :=
  ∀ i < ls.length, P ls[i]!

inductive type
| boolean
| nat
| arr (tp : type) (ct : type)
| rcd (tps : List type) (tpl : SList Label)
| top
deriving Inhabited

inductive WellFormedType : type → Prop
| boolean : WellFormedType type.boolean
| nat : WellFormedType type.nat
| arr (tp ct : type) :
  WellFormedType tp →
  WellFormedType ct →
  WellFormedType (type.arr tp ct)
| rcd (tps : List type) (tpl : SList Label) :
  tpl.length = tps.length →
  (∀ i < tps.length, WellFormedType tps[i]!) →
  WellFormedType (type.rcd tps tpl)
| top : WellFormedType type.top

inductive SubT : type → type → Prop
| Refl (s : type) :
  WellFormedType s →
  SubT s s
| Trans (s u v : type) :
  SubT s u →
  SubT u v →
  SubT s v
| Top (s : type) :
  WellFormedType s →
  SubT s (.top)
| Arrow (s1 s2 t1 t2 : type) :
  SubT t1 s1 →
  SubT s2 t2 →
  SubT (.arr s1 s2) (.arr t1 t2)
| RcdWidth (tpl tpl': SList Label) (tps tps' : List type) :
  tpl.length = tps.length →
  tpl'.length = tps'.length →
  tpl'.IsPrefix tpl →
  tps'.IsPrefix tps →
  (forall_valid tps WellFormedType) →
  (forall_valid tps' WellFormedType) →
  SubT (.rcd tps tpl) (.rcd tps' tpl')
| RcdDepth (tpl : SList Label) (tps tps' : List type) :
  tpl.length = tps.length →
  tpl.length = tps'.length →
  (forall_valid tps WellFormedType) →
  (forall_valid tps' WellFormedType) →
  (∀ i < tps.length, SubT tps'[i]! tps[i]!) →
  SubT (.rcd tps' tpl) (.rcd tps tpl)
| RcdPerm (tpl tpl': SList Label) (tps tps': List type) :
  tpl.length = tps.length →
  tpl'.length = tps'.length →
  (forall_valid tps WellFormedType) →
  (forall_valid tps' WellFormedType) →
  (∀ i < tpl.length, ∃ j < tpl'.length,
    tpl.elems[i]! = tpl'.elems[j]! ∧ tps[i]! = tps'[j]!) →
  SubT (.rcd tps' tpl') (.rcd tps tpl)

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
  tpl.length = tpt.length →
  (∀ i < tpt.length, Value tpt[i]!) →
  Value (Term.Rcd tpt tpl)

abbrev TCtx := List type

@[simp, grind]
def TCtx.types (Γ : TCtx) (x : Nat) (tp : type) : Prop := Γ[x]? = some tp

@[simp, grind]
def TCtx.insert (Γ : TCtx) (tp : type) : TCtx := tp :: Γ

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
  WellFormedType tp →
  Γ.types x tp →
  Typ Γ (.Var x) tp
| TAbs (t : Term) (Γ : TCtx) (tp₁ tp₂ : type) :
  WellFormedType tp₁ →
  Typ (Γ.insert tp₁) t tp₂ →
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
| TRcd (terms: List Term) (labels : SList Label) (Γ : TCtx) (tps : List type) :
  labels.length = tps.length →
  labels.length = terms.length →
  (∀ i < terms.length, Typ Γ terms[i]! tps[i]!) →
  Typ Γ (.Rcd terms labels) (.rcd tps labels)
| TProj (t : Term) (l : Label) (tpl : SList Label)
        (Γ : TCtx)  (tps : List type) (tp : type) :
  Typ Γ t (.rcd tps tpl) →
  tpl.assoc l tps tp →
  (forall_valid tps WellFormedType) →
  Typ Γ (.Proj t l) tp
| TSub (t : Term) (S T : type) (Γ : TCtx):
  Typ Γ t S →
  SubT S T →
  Typ Γ t T

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
  (∀ j < i, Value tpt[j]!) →
  Step tpt[i]! t →
  Step (.Rcd tpt tpl) (.Rcd (tpt.set i t) tpl)
| Proj (t t' : Term) (l : Label) :
  Step t t' →
  Step (.Proj t l) (.Proj t' l)
| ProjRcd (tpt : List Term) (tpl : SList Label) (l : Label)(t : Term) :
  Value (.Rcd tpt tpl) →
  tpl.assoc l tpt t →
  Step (.Proj (.Rcd tpt tpl) l) t

lemma beta_typ (tp : type) (S : type) :
  Γ₂ = Γ₁ ++ Γ → Typ Γ₂ s S → Typ (Γ₁ ++ tp :: Γ) (shift_up_from Γ₁.length s) S := by
  intro hs hs1
  induction hs1 generalizing Γ₁ Γ <;> try grind [Typ, shift_up_from]

lemma betar_preservation (t s : Term) (S T : type) (Γ Γ₁ : TCtx) :
  Γ₂ = Γ₁ ++ S :: Γ → Typ (Γ₁ ++ Γ) s S → Typ Γ₂ t T → Typ (Γ₁ ++ Γ) (betar Γ₁.length t s) T := by
    intro heq hs ht
    unhygienic induction ht generalizing Γ₁ S s
    case TAbs =>
      rw [betar]
      apply Typ.TAbs
      · assumption
      · have ih := a_ih (shift_up s) S (tp₁ :: Γ₁) (by grind) (by
          rw [shift_up]
          have typ_lm := beta_typ tp₁ S (Γ₁ := []) (Γ := Γ₁ ++ Γ) (by grind) hs
          grind)
        grind
    case TVar =>
      rw [betar]
      repeat' split <;> grind [Typ]
    all_goals (grind [Typ, betar])

lemma subtyp_is_well_formed {S T : type} (hs : SubT S T) : WellFormedType S ∧ WellFormedType T := by
  induction hs
  all_goals (try grind [SubT, WellFormedType])

lemma typ_is_well_formed {t : Term} {tp : type} (h : Typ Γ t tp) : WellFormedType tp := by
  induction h
  all_goals (try grind [Typ, WellFormedType, subtyp_is_well_formed])

lemma typ_respects_length {tpl : SList Label} {tps : List type}
  (h : Typ Γ t (.rcd tps tpl)) : tps.length = tpl.length := by
  generalize h1 : type.rcd tps tpl = T at h
  induction h generalizing tps tpl <;> cases h1
  case TApp =>
    rename_i ht _
    apply typ_is_well_formed at ht
    grind [WellFormedType]
  case TSub =>
    rename_i hs
    apply subtyp_is_well_formed at hs
    grind [WellFormedType]
  all_goals (try grind [WellFormedType, typ_is_well_formed])

lemma rcd_proj_sub {tpl : SList Label} {tps : List type}
  (he : tpl.length = tps.length) (hs : SubT S (.rcd tps tpl)) :
  ∃ tpl' tps', S = (.rcd tps' tpl') ∧ tpl'.length = tps'.length ∧
     ∀ l tp, tpl.assoc l tps tp → ∃ tp', SubT tp' tp ∧ tpl'.assoc l tps' tp' := by
  generalize h1 : type.rcd tps tpl = T at hs
  induction hs generalizing tps tpl <;> cases h1
  · exists tpl
    exists tps
    repeat (constructor <;> try assumption)
    intro l tp ha
    exists tp
    grind [SubT, WellFormedType]
  · rename_i ih1 _ ih2
    rcases ih2 he (by rfl) with ⟨tpl', tps', hs, hl, ha⟩
    rcases ih1 hl (by grind) with ⟨tpl'', tps'', hs', hl', ha'⟩
    exists tpl''
    exists tps''
    repeat (constructor <;> try assumption)
    intro l tp hla
    have ⟨tp', htp, hl'⟩ := ha l tp hla
    have ⟨tp'', htp', hl''⟩ := ha' l tp' hl'
    exists tp''
    grind [SubT]
  · rename_i tpl1 tpl2 tps1 tps2 _ _ _ hps _ _
    have hpl : tpl2.elems.IsPrefix tpl1.elems := by grind [SList.IsPrefix]
    exists tpl1
    exists tps1
    repeat (constructor <;> try assumption)
    intro l tp ha
    exists tp
    constructor
    · grind [SubT]
    · rcases ha with ⟨i, hi, heql, heqs⟩
      grind [List.prefix_iff_getElem?.mp hpl i, List.prefix_iff_getElem?.mp hps i]
  · rename_i tpl tps tps' _ _ ihs ih _ _
    exists tpl
    exists tps'
    repeat (constructor <;> try grind)
  · rename_i tpl1 tpl2 tps1 tps2 _ _ _ _ ih
    exists tpl2
    exists tps2
    repeat (constructor <;> try grind)
    intro l tp ha
    rcases ha with ⟨i, hi, heql, heqs⟩
    have ⟨j, _, _, _⟩ := ih i hi
    exists tps2[j]!
    grind [SubT]

lemma rcd_typ {tpt : List Term} {tps : List type}
  {tpl1 tpl2 : SList Label} {tp : type}
  (he : tpl2.length = tps.length)
  (ht : Typ Γ (.Rcd tpt tpl1) (.rcd tps tpl2))
  (hts : tpl2.assoc l tps tp) (htt : tpl1.assoc l tpt t) : Typ Γ t tp := by
  generalize h1 : Term.Rcd tpt tpl1 = t₁ at ht
  generalize h2 : type.rcd tps tpl2 = tp₁ at ht
  induction ht generalizing tps tpl2 tp
  all_goals (try contradiction)
  · grind [List.Nodup.getElem_inj_iff]
  · cases h1
    cases h2
    rename_i ht ih hs
    rcases rcd_proj_sub he hs with ⟨tpl', tps', _, _, ha⟩
    rcases ha l tp hts with ⟨tp', hstp, ha'⟩
    grind [Typ]

lemma arr_subt (sh : SubT S T) (h : t₁.arr t₂ = T) :
  ∃ s₁ s₂, SubT t₁ s₁ ∧ SubT s₂ t₂ ∧ S = (.arr s₁ s₂) := by
  induction sh generalizing t₁ t₂
  case Trans =>
    rename_i ih1 ih2
    rcases ih2 h with ⟨s₁, s₂, hs1, hs2, hu⟩
    rcases ih1 hu.symm with ⟨s₃, s₄, hs3, hs4, hp⟩
    grind [SubT]
  all_goals (grind [SubT, WellFormedType])

lemma ctx_subt (sh : SubT s₁ s₂)
  (ht : Typ (Γ ++ s₂ :: Γ') t T) : Typ (Γ ++ s₁ :: Γ') t T := by
  generalize h1 : Γ ++ s₂ :: Γ' = Γ₁ at ht
  induction ht generalizing Γ
  case TVar =>
    rename_i x _ tp htyp _
    by_cases h : x = Γ.length
    · have he : tp = s₂ := by grind
      apply Typ.TSub (S := s₁)
      · grind [Typ, subtyp_is_well_formed]
      · grind
    · grind [Typ]
  all_goals (try grind [Typ])

lemma abs_typ {tp tp₁ tp₂ : type}
  (h : Typ Γ (t.Abs tp) (tp₁.arr tp₂)) :
  Typ (tp₁ :: Γ) t tp₂ := by
  generalize h1 : t.Abs tp = t' at h
  generalize h2 : tp₁.arr tp₂ = tp' at h
  induction h generalizing tp₁ tp₂
  all_goals (try contradiction)
  · grind [Typ]
  · rename_i ih
    rcases arr_subt (by assumption) (by assumption) with ⟨s₁, s₂, hs1, hs2, hp⟩
    have _ := ih h1 hp.symm
    apply Typ.TSub
    · apply ctx_subt (Γ := [])
      · assumption
      · assumption
    · assumption

theorem preservation (t t' : Term) (tp : type) (Γ : TCtx) :
  Step t t' → Typ Γ t tp → Typ Γ t' tp := by
    intro hs ht
    induction ht generalizing t'
    case TApp =>
      cases hs
      repeat grind [Typ]
      apply betar_preservation (Γ₁ := [])
      · rfl
      · assumption
      · apply abs_typ
        assumption
    case Tite =>
      cases hs <;> grind [Typ]
    case TSucc =>
      cases hs
      grind [Typ]
    case TPred =>
      cases hs
      repeat grind [Typ]
      rename_i nv _ _
      clear * - nv
      induction nv <;> grind [NatValue, Typ]
    case TIsZero =>
      cases hs
      repeat grind [Typ]
    case TRcd =>
      cases hs
      constructor
      repeat grind
    case TProj =>
      cases hs <;> grind [Typ, rcd_typ, typ_respects_length]
    all_goals (grind [Step, Typ])

lemma nat_value_from (ht : Typ Γ t type.nat) (hv : Value t) : NatValue t := by
  sorry
  -- cases ht <;> cases hv <;> grind

lemma bool_value_from (ht : Typ Γ t type.boolean) (hv : Value t) :
  t = .trueT ∨ t = .falseT := by
  sorry
  -- cases ht <;> cases hv
  -- all_goals (try contradiction)
  -- · grind
  -- · grind

lemma rcd_value_from (tpl : SList Label) (tps : List type)
  (ht : Typ Γ t (.rcd tps tpl)) (hv : Value t) :
  ∃ tpt, t = .Rcd tpt tpl ∧ tpt.length = tps.length ∧
  (∀ i < tps.length, Typ Γ tpt[i]! tps[i]! ∧ Value tpt[i]!) := by
  sorry
  -- cases ht <;> cases hv
  -- all_goals (try contradiction)
  -- grind

lemma p_prefix [Inhabited α] {P : α → Prop} (ls : List α) (h : ∃ i < ls.length, ¬P ls[i]!) :
  ∃ i < ls.length, ¬P ls[i]! ∧ ∀ j < i, P ls[j]! := by
  induction ls using List.reverseRecOn
  · grind
  · rename_i p a ih
    by_cases hp : ∃ j < p.length, ¬P p[j]!
    · apply ih at hp
      have ⟨ i, _ ⟩ := hp
      exists i
      grind
    · grind

theorem progress (t : Term) (td : Typ [] t T) :
  Value t ∨ ∃ t', Step t t' := by
  sorry
  -- generalize h : [] = Γ at td
  -- induction td
  -- · grind [Value]
  -- · grind [Value]
  -- · grind
  -- · grind [Value]
  -- · rename_i ht _ ih1 ih2
  --   cases ih1 h
  --   · rename_i tp₁ tp₂ a hv
  --     generalize hp : tp₁.arr tp₂ = tp at ht
  --     cases ht <;> cases hv
  --     all_goals (try contradiction)
  --     cases ih2 h
  --     · rename_i t2 _ t _ _ _ _
  --       right
  --       exists subst t t2
  --       solve_by_elim
  --     · rename_i t tp _ _  hs
  --       have ⟨ t2', _ ⟩ := hs
  --       right
  --       exists (t.Abs tp).App t2'
  --       solve_by_elim
  --   · rename_i t2 _ _ _ _ hs
  --     have ⟨ t1', _ ⟩ := hs
  --     right
  --     exists (.App t1' t2)
  --     solve_by_elim
  -- · rename_i ihc iht ihe
  --   cases ihc h
  --   · rename_i t1 t2 _ _ _ _ _ _
  --     right
  --     cases bool_value_from (by assumption) (by assumption)
  --     · exists t1
  --       rename_i hc
  --       rw [hc]
  --       solve_by_elim
  --     · exists t2
  --       rename_i hc
  --       rw [hc]
  --       solve_by_elim
  --   · rename_i t1 t2 _ _ _ _ _ hs
  --     have ⟨ ct', _ ⟩ := hs
  --     right
  --     exists (.ite ct' t1 t2)
  --     solve_by_elim
  -- · grind [Value, NatValue]
  -- · rename_i ih
  --   cases ih h
  --   · cases nat_value_from (by assumption) (by assumption)
  --     · grind [Value, NatValue]
  --     · grind [Value, NatValue]
  --   · rename_i hs
  --     have ⟨ t', _ ⟩ := hs
  --     right
  --     exists (.Succ t')
  --     solve_by_elim
  -- · rename_i ih
  --   cases ih h
  --   · cases nat_value_from (by assumption) (by assumption)
  --     · right
  --       exists .Zero
  --       solve_by_elim
  --     · rename_i t _ _ _
  --       right
  --       exists t
  --       solve_by_elim
  --   · rename_i hs
  --     have ⟨ t', _ ⟩ := hs
  --     right
  --     exists (.Pred t')
  --     solve_by_elim
  -- · rename_i ht ih
  --   cases ih h
  --   · rename_i hv
  --     have nv := nat_value_from (by assumption) hv
  --     right
  --     cases nv
  --     · exists .trueT
  --       solve_by_elim
  --     · exists .falseT
  --       solve_by_elim
  --   · rename_i hs
  --     have ⟨ t', _ ⟩ := hs
  --     right
  --     exists (.IsZero t')
  --     solve_by_elim
  -- · rename_i tpt tpl _ tps h1 h2 hl ih
  --   by_cases hv : ∀ i < tpt.length, Value tpt[i]!
  --   · left
  --     grind [Value]
  --   · have ⟨ i, hi, hnv, hvs ⟩ : ∃ i < tpt.length,
  --           ¬Value tpt[i]! ∧ ∀ j < i, Value tpt[j]! := by
  --       apply p_prefix
  --       grind
  --     have ⟨ t', _ ⟩ : ∃ t', Step tpt[i]! t' := by grind
  --     right
  --     exists (.Rcd (tpt.set i t') tpl)
  --     grind [Step]
  -- · rename_i ih
  --   cases ih h
  --   · cases rcd_value_from _ _ (by assumption) (by assumption)
  --     rename_i ah _ tpt _
  --     rcases ah with ⟨ i, _, _, _ ⟩
  --     right
  --     exists tpt[i]!
  --     grind [Step]
  --   · rename_i hs
  --     have ⟨ t', _ ⟩ := hs
  --     right
  --     exists (.Proj t' (by assumption))
  --     grind [Step]

end Subtyping
