import OAI.Computability.VPVNP.LiveHeaderCutInput
import OAI.Computability.VPVNP.LiveHeaderMode
import OAI.Computability.VPVNP.LivePhysicalContraction

/-!
# Physical mode selection and the unit group count

The mode table reads slots two and three of processor zero and the widths
of the two cuts. Its unit tag, followed by the two padding scans, is
equivalent to the unit summand of the contraction. Its other tag selects
the evaluation summand of the first half or the tail, including at both
ends and when adjacent cuts have incompatible modes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeader

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM ChainAssignments
open CutSchedule LiveHeaderDescriptors
open scoped Classical Fin.CommRing

variable {w d a h Δ t Z M : ℕ}

/-- The scheduled width of the cut incident to the given side of a group. -/
abbrev incidentWidth (side : Side) (g : Fin (2^(h+1))) :=
  width (h+1) Δ (incidentCut side g).val

/-- The Boolean test that a group lies in the initial half of the chain. -/
def firstHalfFlag (g : Fin (2^(h+1))) := decide (g.val+1 ≤ 2^h)

/-- The tag computed from the actual incident widths and processor-zero bits. -/
def physicalTag (cuts : AllCuts h Δ) (g : Fin (2^(h+1))) :=
  Mode.selected (incidentWidth (Δ := Δ) .left g) (incidentWidth (Δ := Δ) .right g)
    (distributedBit (cuts g.castSucc) 0) (distributedBit (cuts g.succ) 0) (firstHalfFlag g)

private theorem width_pos_iff {H j : ℕ} (hΔ : 0 < Δ) :
    0 < width H Δ j ↔ 0 < j ∧ j < 2^H := by
  rw [width]
  by_cases hj : 0 < j ∧ j < 2^H
  · rw [ite_eq_left hj]
    have hlog := Nat.log_lt_of_lt_pow hj.1.ne' hj.2
    exact iff_of_true (Nat.mul_pos (by omega) hΔ) hj
  · simp [hj]

private theorem has_incident (hΔ : 0 < Δ) (g : Fin (2^(h+1))) :
    incidentWidth (Δ := Δ) .left g ≠ 0 ∨ incidentWidth (Δ := Δ) .right g ≠ 0 := by
  by_cases first : g.val = 0
  · apply Or.inr
    apply Nat.ne_of_gt ((width_pos_iff hΔ).mpr ?_)
    change 0 < g.val+1 ∧ g.val+1 < 2^(h+1)
    rw [first, Nat.zero_add]
    exact ⟨by decide, Nat.one_lt_two_pow (by omega)⟩
  · apply Or.inl
    exact Nat.ne_of_gt ((width_pos_iff hΔ).mpr ⟨Nat.pos_of_ne_zero first,g.isLt⟩)

private theorem selected_iff {l r : ℕ} (present : l ≠ 0 ∨ r ≠ 0) (x y f : Bool) :
    (Mode.selected l r x y f = some .unit ↔ (l = 0 ∨ x = false) ∧ (r = 0 ∨ y = false)) ∧
    (Mode.selected l r x y f = some (Mode.selectTag true f) ↔ (l = 0 ∨ x = true) ∧ (r = 0 ∨ y = true)) := by
  by_cases hl : l = 0 <;> by_cases hr : r = 0 <;> cases x <;> cases y <;> cases f <;>
    simp [Mode.selected,Mode.selectTag,hl,hr] at *

private theorem eval_mode_iff (hΔ : 0 < Δ) (cuts : AllCuts h Δ) (i : Fin (2^(h+1)+1)) :
    evalCutMode cuts i ↔ width (h+1) Δ i.val = 0 ∨ distributedBit (cuts i) 0 = true := by
  have hp := width_pos_iff (j := i.val) (H := h+1) hΔ
  constructor
  · intro he
    by_cases hz : width (h+1) Δ i.val = 0
    · exact Or.inl hz
    · have ⟨a,b⟩ := hp.mp (Nat.pos_of_ne_zero hz)
      exact Or.inr (he a b)
  · rintro (hz | hb) a b
    · exact False.elim ((hp.mpr ⟨a,b⟩).ne' hz)
    · exact hb

/-- Evaluation is selected exactly when both actual interior modes are true.
The first-half flag distinguishes the pair and tail tags. -/
theorem physicalTag_evaluation (hΔ : 0 < Δ) (cuts : AllCuts h Δ) (g : Fin (2^(h+1))) :
    physicalTag cuts g = some (Mode.selectTag true (firstHalfFlag g)) ↔
      evalCutMode cuts g.castSucc ∧ evalCutMode cuts g.succ := by
  rw [eval_mode_iff hΔ, eval_mode_iff hΔ]
  exact (selected_iff (has_incident hΔ g) _ _ _).2

private theorem mode_site_zero_iff {W : ℕ} (bits : Bits W) :
    (W = 0 ∨ distributedBit bits 0 = false) ↔ ∀ i : Fin W, i.val = 0 → bits i = false := by
  by_cases hz : 0 < W
  · simp only [hz.ne',false_or,distributedBit,dite_eq_left hz]
    constructor
    · intro zero i hi
      exact (congrArg bits (Fin.ext hi)).trans zero
    · exact fun zero => zero ⟨0,hz⟩ rfl
  · have hW : W = 0 := by omega
    exact iff_of_true (Or.inl hW) (fun i _ => False.elim (by have := i.isLt; omega))

/-- The two trailing padding intervals in unit mode. They may be empty. -/
def unitPads (cuts : AllCuts h Δ) (g : Fin (2^(h+1))) (e c : ℕ) : Prop :=
  ∀ side, Physical.ZeroSlice (cuts (incidentCut side g))
    (span .unit (incidentWidth (Δ := Δ) side g) Δ e c .padding)

/-- Both complete cuts are zero precisely when the physical table chooses
the unit tag and the two padding intervals pass. -/
theorem physicalTag_unit (hΔ : 0 < Δ) (cuts : AllCuts h Δ) (g : Fin (2^(h+1))) (e c : ℕ) :
    (physicalTag cuts g = some .unit ∧ unitPads cuts g e c) ↔
      cuts g.castSucc = (fun _ => false) ∧ cuts g.succ = (fun _ => false) := by
  have hu := (selected_iff (has_incident hΔ g) (distributedBit (cuts g.castSucc) 0)
    (distributedBit (cuts g.succ) 0) (firstHalfFlag g)).1
  constructor
  · rintro ⟨tag,pads⟩
    have ht := hu.mp tag
    exact ⟨funext ((Physical.unit_zero_iff _ Δ e c).mp ⟨(mode_site_zero_iff _).mp ht.1,pads .left⟩),
      funext ((Physical.unit_zero_iff _ Δ e c).mp ⟨(mode_site_zero_iff _).mp ht.2,pads .right⟩)⟩
  · rintro ⟨hl,hr⟩
    have left := (Physical.unit_zero_iff _ Δ e c).mpr (congrFun hl)
    have right := (Physical.unit_zero_iff _ Δ e c).mpr (congrFun hr)
    refine ⟨hu.mpr ⟨(mode_site_zero_iff _).mpr left.1,(mode_site_zero_iff _).mpr right.1⟩,?_⟩
    intro side
    cases side
    · exact left.2
    · exact right.2

private theorem unit_span_fit (W Δ e c : ℕ) :
    let iv := span .unit W Δ e c .padding
    iv.1+iv.2 ≤ W := by
  dsimp [span,count,start,mode,exterior,exponents,config]
  split_ifs <;> omega

/-- The native padding scan for the selected side succeeds on its full deterministic sequence
of calls. -/
abbrev PaddingSuccess (side : Side) (pub : Fin 3 → Word w) (m : Memory w) (len : ℕ) : Prop :=
  let P := ((template (checkPaddingCell (cutSlot side)) 7).instantiate w pub).program
  (runSegment P 15 (some (pub 0)) m (List.replicate len [])).isSome = true

/-- Native acceptance of the two unit-padding scans, on the actual packed
headers and descriptor words, computes exactly the unit contribution. -/
theorem native_unit_count {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ}
    {g : Fin (2^(h+1))} {m : Memory w} (hΔ : 0 < Δ) (headers : SiteHeaders d hw advice cuts g m)
    (e c : ℕ) (pub : Side → Fin 3 → Word w)
    (source : ∀ side, (m (pub side 1).val).val = (span .unit (incidentWidth (Δ := Δ) side g) Δ e c .padding).1)
    (sites : ∀ side, incidentWidth (Δ := Δ) side g ≤ 2^d) (fit : 2^d ≤ 2^w) :
    (if physicalTag cuts g = some .unit ∧
      (∀ side, PaddingSuccess side (pub side) m (span .unit (incidentWidth (Δ := Δ) side g) Δ e c .padding).2)
    then 1 else 0) = unitGroupCount cuts g := by
  have h (side : Side) := physical_padding_native_iff headers side
    (span .unit (incidentWidth (Δ := Δ) side g) Δ e c .padding) (pub side) (source side)
    ((unit_span_fit ..).trans (sites side)) (unit_span_fit ..) ((unit_span_fit ..).trans ((sites side).trans fit))
  have hp : (∀ side, PaddingSuccess side (pub side) m
      (span .unit (incidentWidth (Δ := Δ) side g) Δ e c .padding).2) ↔ unitPads cuts g e c :=
    forall_congr' h
  apply ite_congr _ (fun _ => rfl) (fun _ => rfl)
  exact propext ((and_congr_right fun _ => hp).trans (physicalTag_unit hΔ cuts g e c))

/-- Public words 0 and 1 address the computed widths. The third scalar is
the first-half flag. From these words the fixed native table realizes
exactly the tag above on physical memory. -/
theorem physical_mode_native {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ}
    {g : Fin (2^(h+1))} {m : Memory w} (headers : SiteHeaders d hw advice cuts g m)
    (pub : Fin 16 → Word w) (state : Word w) (tag : Mode.Tag)
    (left : (m (pub 0).val).val = incidentWidth (Δ := Δ) .left g)
    (right : (m (pub 1).val).val = incidentWidth (Δ := Δ) .right g)
    (flag : m (pub 2).val = PrimedInputRAM.encodeBit w (firstHalfFlag g)) (sel : physicalTag cuts g = some tag) :
    let v := Fin.ofNat (2^w) tag.code.val
    let P := ((Mode.program.template none).instantiate w pub).program
    ∃ es, execute P 25 (P.start state) m [] = some ⟨es,none⟩ ∧
      es.length ≤ 24 ∧ countProbes es = 5 ∧ choiceBits es = [] ∧ after m es = writeMemory m (pub 3) v := by
  let zero : Fin (2^d) := ⟨0,Nat.two_pow_pos _⟩
  apply Mode.native_selected pub state m hw (physicalHeader advice cuts g zero) (firstHalfFlag g) tag
    (headers zero) flag
  rw [left,right]
  exact sel

/-- When the two occupied modes disagree the native dispatcher rejects at
all fuel bounds and for every nondeterministic choice tape. -/
theorem physical_mode_rejects {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ}
    {g : Fin (2^(h+1))} {m : Memory w} (headers : SiteHeaders d hw advice cuts g m)
    (pub : Fin 16 → Word w) (state : Word w)
    (left : (m (pub 0).val).val = incidentWidth (Δ := Δ) .left g)
    (right : (m (pub 1).val).val = incidentWidth (Δ := Δ) .right g)
    (flag : m (pub 2).val = PrimedInputRAM.encodeBit w (firstHalfFlag g)) (sel : physicalTag cuts g = none)
    (fuel : ℕ) (bits : List Bool) :
    let P := ((Mode.program.template none).instantiate w pub).program
    execute P fuel (P.start state) m bits = none := by
  let zero : Fin (2^d) := ⟨0,Nat.two_pow_pos _⟩
  apply Mode.native_rejected pub state m hw (physicalHeader advice cuts g zero) (firstHalfFlag g)
    (headers zero) flag _ fuel bits
  rw [left,right]
  exact sel

private theorem selected_cases (l r : ℕ) (x y f : Bool) :
    Mode.selected l r x y f = none ∨ Mode.selected l r x y f = some .unit ∨
    Mode.selected l r x y f = some (Mode.selectTag true f) := by
  unfold Mode.selected
  split_ifs <;> cases x <;> cases y <;> simp [Mode.selectTag]

/-- The pair tag occurs precisely on evaluation-mode groups of the first half. -/
theorem physicalTag_pair (hΔ : 0 < Δ) (cuts : AllCuts h Δ) (g : Fin (2^(h+1))) :
    physicalTag cuts g = some .pair ↔
      (evalCutMode cuts g.castSucc ∧ evalCutMode cuts g.succ) ∧ g.val+1 ≤ 2^h := by
  have eval := physicalTag_evaluation hΔ cuts g
  have casesTag := selected_cases (incidentWidth (Δ := Δ) .left g) (incidentWidth (Δ := Δ) .right g)
    (distributedBit (cuts g.castSucc) 0) (distributedBit (cuts g.succ) 0) (firstHalfFlag g)
  change physicalTag cuts g = none ∨ physicalTag cuts g = some .unit ∨
    physicalTag cuts g = some (Mode.selectTag true (firstHalfFlag g)) at casesTag
  by_cases hf : g.val+1 ≤ 2^h
  · simpa [firstHalfFlag,Mode.selectTag,hf] using eval
  · simp only [hf,and_false,iff_false]
    rcases casesTag with hs | hs | hs <;> simp [hs,Mode.selectTag,firstHalfFlag,hf]

/-- The tail tag occurs precisely on evaluation-mode groups after the midpoint. -/
theorem physicalTag_tail (hΔ : 0 < Δ) (cuts : AllCuts h Δ) (g : Fin (2^(h+1))) :
    physicalTag cuts g = some .tail ↔
      (evalCutMode cuts g.castSucc ∧ evalCutMode cuts g.succ) ∧ 2^h < g.val+1 := by
  have eval := physicalTag_evaluation hΔ cuts g
  have casesTag := selected_cases (incidentWidth (Δ := Δ) .left g) (incidentWidth (Δ := Δ) .right g)
    (distributedBit (cuts g.castSucc) 0) (distributedBit (cuts g.succ) 0) (firstHalfFlag g)
  change physicalTag cuts g = none ∨ physicalTag cuts g = some .unit ∨
    physicalTag cuts g = some (Mode.selectTag true (firstHalfFlag g)) at casesTag
  by_cases hf : g.val+1 ≤ 2^h
  · simp only [hf.not_gt,and_false,iff_false]
    rcases casesTag with hs | hs | hs <;> simp [hs,Mode.selectTag,firstHalfFlag,hf]
  · simpa [firstHalfFlag,Mode.selectTag,hf,Nat.lt_of_not_ge hf] using eval

/-- Dispatching by the actual mode-table result, with unit and evaluation
branches enforcing their respective checks. -/
noncomputable def routedCount (tag : Option Mode.Tag) (unitPad incoming : Prop) (count : ℕ) : ℕ :=
  match tag with
  | none => 0
  | some .unit => if unitPad then 1 else 0
  | some .pair | some .tail => if incoming then count else 0

private theorem routedCount_eq (tag : Option Mode.Tag) (pad incoming : Prop) (count : ℕ) :
    routedCount tag pad incoming count =
      (if tag = some .unit ∧ pad then 1 else 0) +
      (if (tag = some .pair ∨ tag = some .tail) ∧ incoming then count else 0) := by
  cases tag with
  | none => simp [routedCount]
  | some x => cases x <;> simp [routedCount]

variable {Nom : Type*} [Fintype Nom] {Path : ExponentTrace.Exterior h Δ → Fin (2^h) → Nom → Type*}
  [∀ ξ i μ, Fintype (Path ξ i μ)]
variable (fit : 1+t*Z ≤ Δ) (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)
  (E : UniversalMachine.Program) (layout : LiveEvaluatorTail.Layout E.extra M w Δ)
  (init : (Fin t → ℕ) → LiveEvaluatorEncoding.Code E.extra M)

/-- The locally specified count on every raw cut assignment is the branch
chosen by the actual dispatcher. This includes malformed and mismatched modes. -/
theorem routed_specifiedGroupCount (cuts : AllCuts h Δ) (g : Fin (2^(h+1))) (e c : ℕ) :
    routedCount (physicalTag cuts g) (unitPads cuts g e c) (incomingChecks t Z layout cuts g)
      (groupEvaluation fit inc E layout init cuts g) = specifiedGroupCount fit inc E layout init cuts g := by
  have hΔ : 0 < Δ := by omega
  have he : (physicalTag cuts g = some .pair ∨ physicalTag cuts g = some .tail) ↔
      evalCutMode cuts g.castSucc ∧ evalCutMode cuts g.succ := by
    rw [physicalTag_pair hΔ,physicalTag_tail hΔ]
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      rcases le_or_gt (g.val+1) (2^h) with hl | hr
      · exact Or.inl ⟨hx,hl⟩
      · exact Or.inr ⟨hx,hr⟩
  rw [routedCount_eq,specifiedGroupCount]
  congr 1
  · exact ite_congr (propext (physicalTag_unit hΔ cuts g e c)) (fun _ => rfl) (fun _ => rfl)
  · apply ite_congr _ (fun _ => rfl) (fun _ => rfl)
    exact propext ((and_congr_left (fun _ => he)).trans and_assoc)

/-- A first-half evaluation tag runs the pair whose raw exterior bits and
cumulative exponent fields occupy these physical cuts. -/
theorem routed_pair_count (cuts : AllCuts h Δ) (i : Fin (2^h)) (e c : ℕ) :
    let g := halves h (.inl i)
    routedCount (physicalTag cuts g) (unitPads cuts g e c) (incomingChecks t Z layout cuts g)
      (pairCount fit inc (liveCutEquiv h Δ cuts).1 i) = specifiedGroupCount fit inc E layout init cuts g := by
  simpa only [groupEvaluation, Equiv.symm_apply_apply, Sum.elim_inl] using
    routed_specifiedGroupCount fit inc E layout init cuts (halves h (.inl i)) e c

/-- The first tail group obtains its initial code from the middle exponents.
Each subsequent group parses the canonical code from its incoming cut. -/
theorem routed_tail_count (cuts : AllCuts h Δ) (i : Fin (2^h)) (e c : ℕ) :
    let g := halves h (.inr i)
    let fst := (liveCutEquiv h Δ cuts).1
    let lst := (liveCutEquiv h Δ cuts).2
    routedCount (physicalTag cuts g) (unitPads cuts g e c) (incomingChecks t Z layout cuts g)
      (tailCount E layout (init (fun a => (ExponentTrace.counters fit fst (Fin.last _) a).val)) lst i) =
      specifiedGroupCount fit inc E layout init cuts g := by
  simpa only [groupEvaluation, Equiv.symm_apply_apply, Sum.elim_inr] using
    routed_specifiedGroupCount fit inc E layout init cuts (halves h (.inr i)) e c

end LiveHeader

end VPVNP
end Computability
end OAI
