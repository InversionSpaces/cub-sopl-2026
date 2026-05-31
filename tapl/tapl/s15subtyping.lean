import Mathlib.Tactic.Basic
import Mathlib.Data.List.Nodup
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
| ProjRcd (tpt : List Term) (tpl : SList Label) (l : Label) (t : Term) :
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

lemma subt_respects_length {tpl : SList Label} {tps : List type}
  (h : SubT S (.rcd tps tpl)) : tpl.length = tps.length := by
  rcases subtyp_is_well_formed h with ⟨_, wf⟩
  generalize he : type.rcd tps tpl = T at wf
  induction wf
  all_goals (try contradiction)
  case rcd =>
    cases he
    grind

-- For this lemma I gave up, proved by an LLM
lemma rcd_proj_sub {tpl : SList Label} {tps : List type} (hs : SubT S (.rcd tps tpl)) :
  ∃ tpl' tps', S = (.rcd tps' tpl') ∧
    tpl'.length = tps'.length ∧ tpl.Subperm tpl' ∧
     ∀ l tp, tpl.assoc l tps tp → ∃ tp', SubT tp' tp ∧ tpl'.assoc l tps' tp' := by
  have he : tpl.length = tps.length := subt_respects_length hs
  generalize hT : type.rcd tps tpl = T at hs
  induction hs generalizing tps tpl
  all_goals (try contradiction)
  · cases hT
    refine ⟨tpl, tps, rfl, ?_, ?_, ?_⟩
    · assumption
    · exact List.Subperm.refl _
    · intro l tp ha
      exact ⟨tp, SubT.Refl _ (by grind [WellFormedType]), ha⟩
  · cases hT
    rename_i ih1 _ ih2
    rcases ih2 he (by rfl) with ⟨tpl', tps', hs, hl, hsp, ha⟩
    rcases ih1 hl hs.symm with ⟨tpl'', tps'', hs', hl', hsp', ha'⟩
    refine ⟨tpl'', tps'', hs', hl', ?_, ?_⟩
    · exact List.Subperm.trans hsp hsp'
    · intro l tp hla
      have ⟨tp', htp, hl''⟩ := ha l tp hla
      have ⟨tp'', htp', hl'''⟩ := ha' l tp' hl''
      exact ⟨tp'', SubT.Trans _ _ _ htp' htp, hl'''⟩
  · rename_i tpl_src tpl_tgt tps_src tps_tgt hlen_src hlen_tgt hpl_pref hps_pref hwf_src hwf_tgt
    cases hT
    have hpl : tpl_tgt.elems.IsPrefix tpl_src.elems := hpl_pref
    refine ⟨tpl_src, tps_src, rfl, hlen_src, ?_, ?_⟩
    · exact List.Sublist.subperm (List.IsPrefix.sublist hpl)
    · intro l tp ha
      rcases ha with ⟨i, hi, heql, heqs⟩
      have hi_tgt : i < tps_tgt.length := by
        have : tpl_tgt.length = tps_tgt.length := hlen_tgt
        grind
      have htp_eq : tps_tgt[i]! = tp := List.getElem!_of_getElem? heqs
      have hwf_tp : WellFormedType tp := htp_eq ▸ hwf_tgt i hi_tgt
      refine ⟨tp, SubT.Refl _ hwf_tp, ?_⟩
      have hi_src_lbl : i < tpl_src.length := by
        have hsub_l : tpl_tgt.elems.length ≤ tpl_src.elems.length := hpl.length_le
        simp only [SList.length] at hi ⊢
        omega
      have hi_lbl_tgt : i < tpl_tgt.elems.length := by simp only [SList.length] at hi; exact hi
      have hi_tps_tgt : i < tps_tgt.length := hi_tgt
      refine ⟨i, hi_src_lbl, ?_, ?_⟩
      · have hp : tpl_src.elems[i]? = some tpl_tgt.elems[i] :=
          List.prefix_iff_getElem?.mp hpl i hi_lbl_tgt
        rw [hp]
        rw [List.getElem?_eq_some_iff] at heql
        exact congrArg some heql.2
      · have hp : tps_src[i]? = some tps_tgt[i] :=
          List.prefix_iff_getElem?.mp hps_pref i hi_tps_tgt
        rw [hp]
        rw [List.getElem?_eq_some_iff] at heqs
        exact congrArg some heqs.2
  · rename_i tpl0 tps_tgt tps_src hlen_tgt hlen_src hwf_tgt hwf_src hsub ih
    cases hT
    refine ⟨tpl0, tps_src, rfl, ?_, List.Subperm.refl _, ?_⟩
    · grind
    · intro l tp ha
      rcases ha with ⟨i, hi, heql, heqs⟩
      have hi_src : i < tps_src.length := by
        have : tpl0.length = tps_src.length := hlen_src
        have : tpl0.length = tps_tgt.length := hlen_tgt
        grind
      have hi_tgt : i < tps_tgt.length := by
        have : tpl0.length = tps_tgt.length := hlen_tgt
        grind
      have heq_tp : tps_tgt[i]! = tp := List.getElem!_of_getElem? heqs
      refine ⟨tps_src[i]!, ?_, ?_⟩
      · have := hsub i hi_tgt
        rw [heq_tp] at this
        exact this
      · refine ⟨i, hi, heql, ?_⟩
        rw [List.getElem?_eq_getElem hi_src, getElem!_pos tps_src i hi_src]
  · rename_i tpl_tgt tpl_src tps_tgt tps_src hlen_tgt hlen_src hwf_tgt hwf_src hcorr
    cases hT
    refine ⟨tpl_src, tps_src, rfl, hlen_src, ?_, ?_⟩
    · have hsubset : ∀ x ∈ tpl_tgt.elems, x ∈ tpl_src.elems := by
        intro x hx
        rcases List.mem_iff_getElem.mp hx with ⟨i, hi, hxi⟩
        have hi_lbl : i < tpl_tgt.elems.length := hi
        have hi' : i < tpl_tgt.length := by simp only [SList.length]; exact hi
        have ⟨j, hj, heq, _⟩ := hcorr i hi'
        have hxi' : tpl_tgt.elems[i]! = x := by
          rw [getElem!_pos tpl_tgt.elems i hi_lbl]; exact hxi
        rw [hxi'] at heq
        rw [heq]
        have hj_lbl : j < tpl_src.elems.length := by simp only [SList.length] at hj; exact hj
        rw [getElem!_pos tpl_src.elems j hj_lbl]
        exact List.getElem_mem hj_lbl
      apply List.subperm_ext_iff.mpr
      intro x hx
      have hmem := hsubset x hx
      have hcount1 : tpl_tgt.elems.count x ≤ 1 := List.nodup_iff_count_le_one.mp tpl_tgt.nodup x
      have hcount2 : 1 ≤ tpl_src.elems.count x := List.count_pos_iff.mpr hmem
      omega
    · intro l tp ha
      rcases ha with ⟨i, hi, heql, heqs⟩
      have hi' : i < tpl_tgt.length := hi
      have hi_lbl : i < tpl_tgt.elems.length := by simp only [SList.length] at hi; exact hi
      have hi_tps_tgt : i < tps_tgt.length := by
        have : tpl_tgt.length = tps_tgt.length := hlen_tgt
        simp only [SList.length] at hi; grind
      have ⟨j, hj, hjl, hjs⟩ := hcorr i hi'
      have hj_lbl : j < tpl_src.elems.length := by simp only [SList.length] at hj; exact hj
      have hj_tps : j < tps_src.length := by
        have : tpl_src.length = tps_src.length := hlen_src
        simp only [SList.length] at hj; grind
      have hl_eq : tpl_tgt.elems[i]! = l := List.getElem!_of_getElem? heql
      have hs_eq : tps_tgt[i]! = tp := List.getElem!_of_getElem? heqs
      have hl_src : tpl_src.elems[j]! = l := by rw [← hjl, hl_eq]
      have hs_src : tps_src[j]! = tp := by rw [← hjs, hs_eq]
      refine ⟨tps_src[j]!, ?_, ?_⟩
      · rw [hs_src]
        exact SubT.Refl _ (hs_eq ▸ hwf_tgt i hi_tps_tgt)
      · refine ⟨j, hj, ?_, ?_⟩
        · rw [List.getElem?_eq_getElem hj_lbl,
              ← getElem!_pos tpl_src.elems j hj_lbl, hl_src]
        · rw [List.getElem?_eq_getElem hj_tps,
              ← getElem!_pos tps_src j hj_tps, hs_src]

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
    rcases rcd_proj_sub hs with ⟨tpl', tps', _, _, _, ha⟩
    rcases ha l tp hts with ⟨tp', hstp, ha'⟩
    grind [Typ]

lemma rcd_proj_typ {tp : type} {tps : List type} {tpl : SList Label}
  (hv : Value t) (ht : Typ Γ t (.rcd tps tpl)) (ha : tpl.assoc l tps tp) :
  ∃ tpt tpl', t = (.Rcd tpt tpl') ∧ tpl'.length = tpt.length ∧
  tpl.Subperm tpl' ∧ ∃ t', tpl'.assoc l tpt t' := by
  generalize hT : type.rcd tps tpl = T at ht
  induction ht generalizing tps tpl tp
  all_goals (try contradiction)
  case TRcd =>
    rename_i tpt tpl' _ tps' _ _ _ _
    exists tpt
    exists tpl'
    constructor
    · rfl
    · constructor
      · assumption
      · cases hT
        rcases ha with ⟨i, _, _, _⟩
        constructor
        · exists tpl'.elems
        · exists tpt[i]!
          grind
  case TSub =>
    rename_i ih
    cases hT
    rcases rcd_proj_sub (by assumption) with ⟨tpl', tps', _, hl', hsp_outer, ha⟩
    rcases ha l tp (by assumption) with ⟨tp', hs', ha'⟩
    rcases ih (tps := tps') (tpl := tpl') hv ha' (by grind)
      with ⟨tpt, tpl'', _, _, hsp_inner, ha''⟩
    refine ⟨tpt, tpl'', ?_, ?_, ?_, ?_⟩
    · assumption
    · assumption
    · exact List.Subperm.trans hsp_outer hsp_inner
    · assumption

lemma arr_subt (sh : SubT S T) (h : t₁.arr t₂ = T) :
  ∃ s₁ s₂, SubT t₁ s₁ ∧ SubT s₂ t₂ ∧ S = (.arr s₁ s₂) := by
  induction sh generalizing t₁ t₂
  case Trans =>
    rename_i ih1 ih2
    rcases ih2 h with ⟨s₁, s₂, hs1, hs2, hu⟩
    rcases ih1 hu.symm with ⟨s₃, s₄, hs3, hs4, hp⟩
    grind [SubT]
  all_goals (grind [SubT, WellFormedType])

lemma bool_subt (sh : SubT S type.boolean) : S = type.boolean := by
  generalize h : type.boolean = T at sh
  induction sh
  all_goals (try contradiction)
  · rfl
  · grind

lemma nat_subt (sh : SubT S type.nat) : S = type.nat := by
  generalize h : type.nat = T at sh
  induction sh
  all_goals (try contradiction)
  · rfl
  · grind

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
  generalize h : type.nat = T at ht
  induction ht <;> cases h
  all_goals (try contradiction)
  · grind [NatValue]
  · cases hv
    grind [NatValue]
  · grind [NatValue, nat_subt]

lemma bool_value_from (ht : Typ Γ t type.boolean) (hv : Value t) :
  t = .trueT ∨ t = .falseT := by
  generalize h : type.boolean = T at ht
  induction ht
  all_goals (try contradiction)
  repeat grind [bool_subt]

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

lemma arr_value {tp1 tp2 : type} (ht : Typ Γ t (.arr tp1 tp2)) (hv : Value t) :
  ∃ t' tp1', t = .Abs t' tp1' ∧ SubT tp1 tp1' := by
  generalize h1 : tp1.arr tp2 = T at ht
  induction ht generalizing tp1 tp2
  all_goals (try contradiction)
  case TAbs =>
    rename_i t' _ tp1' _ _ _ _
    exists t'
    exists tp1'
    grind [Typ, SubT]
  case TSub =>
    rename_i ih
    cases h1
    rename_i hs
    cases hs
    · grind
    · rename_i hsSu hsu
      rcases arr_subt hsu (by rfl) with ⟨_, _, _, _, hp⟩
      cases hp
      rcases arr_subt hsSu (by rfl) with ⟨_, _, _, _, hp⟩
      cases hp
      grind [SubT]
    · grind [SubT]

theorem progress (t : Term) (td : Typ [] t T) :
  Value t ∨ ∃ t', Step t t' := by
  generalize h : [] = Γ at td
  induction td <;> cases h
  case Ttrue => grind [Value]
  case Tfalse => grind [Value]
  case TVar => grind
  case TAbs => grind [Value]
  case TZero => grind [Value, NatValue]
  case TApp =>
    rename_i t1 t2 _ _ _ _ ih1 ih2
    cases ih1 rfl <;> cases ih2 rfl <;> right
    · rcases arr_value (by assumption) (by assumption) with ⟨t', tp1', he, hs⟩
      cases he
      exists (subst t' t2)
      grind [Step]
    · rename_i hs
      have ⟨t', hs'⟩ := hs
      exists (t1.App t')
      grind [Step]
    · rename_i hs _
      have ⟨t', hs'⟩ := hs
      exists (t'.App t2)
      grind [Step]
    · rename_i hs _
      have ⟨t', hs'⟩ := hs
      exists (t'.App t2)
      grind [Step]
  case Tite =>
    right
    rename_i t1 t2 _ _ _ _ cih _ _
    cases cih rfl
    · cases bool_value_from (by assumption) (by assumption)
      · exists t1
        grind [Step]
      · exists t2
        grind [Step]
    · rename_i hs
      have ⟨t', _⟩ := hs
      exists (.ite t' t1 t2)
      grind [Step]
  case TSucc =>
    rename_i ih
    cases ih rfl
    · grind [Value, NatValue, nat_value_from]
    · right
      rename_i hs
      have ⟨t', _⟩ := hs
      exists (.Succ t')
      grind [Step]
  case TPred =>
    rename_i ih
    cases ih rfl
    · cases nat_value_from (by assumption) (by assumption)
      · right
        exists .Zero
        grind [Step]
      · right
        rename_i t' _ _ _
        exists t'
        grind [Step]
    · rename_i hs
      have ⟨t', _⟩ := hs
      right
      exists (.Pred t')
      grind [Step]
  case TIsZero =>
    rename_i ih
    cases ih rfl
    · cases nat_value_from (by assumption) (by assumption)
      · right
        exists .trueT
        grind [Step]
      · right
        exists .falseT
        grind [Step]
    · rename_i hs
      have ⟨t', _⟩ := hs
      right
      exists (.IsZero t')
      grind [Step]
  case TRcd =>
    rename_i tpt tpl tps _ _ _ ih
    by_cases h : ∃ i < tpt.length, ¬Value tpt[i]!
    · have ⟨i, hl, hnv, hp⟩ := p_prefix (P := fun t => Value t) tpt h
      right
      cases ih i hl rfl
      · contradiction
      · rename_i hs
        have ⟨t', _⟩ := hs
        exists (.Rcd (tpt.set i t') tpl)
        grind [Step]
    · grind [Value]
  case TProj =>
    rename_i l tpl tps tp ha _ _ ih
    cases ih rfl
    · right
      rename_i hv
      rcases rcd_proj_typ hv (by assumption) ha
        with ⟨tpt, tpl', he, hl, _, t', ha'⟩
      cases he
      exists t'
      grind [Step]
    · rename_i hs
      have ⟨t', _⟩ := hs
      right
      exists (.Proj t' l)
      grind [Step]
  case TSub =>
    rename_i ih
    exact ih rfl

end Subtyping
