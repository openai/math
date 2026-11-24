import OAI.Computability.VPVNP.PairSimulationMapResidentRows
import OAI.Computability.VPVNP.PairSimulationResidentMapLoop
import OAI.Computability.VPVNP.PairShrinkRoleMapLabels
import OAI.Computability.VPVNP.PairRefreshTraversalMapBody
import OAI.Computability.VPVNP.PairShrinkJobPrepared

/-!
# Label counts of native shrinking and refresh rows

A successful motif invocation emits one label for each repetition, including
repeated labels. A shrinking row enumerates the six-party occurrences in its
published order. Its output on every input is bounded by the row capacity
times the repetition bound of the input state. A refresh has one invocation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open MotifGrid MotifBlocks MotifConversion MotifDemandPadding MotifSelector

variable {K : Type*} [Field K] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
    {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
    (B : FixedBlock K a b P (realWidths p) (realWidths q) H H')

/-- A successful run on arbitrary bit inputs emits one base-matrix label
per copy, even if several copies select the same label. -/
theorem runEntry_length [DecidableEq J] (hp : ∀ i, 0 < p i) (width : D → ℕ)
    (payload : S → ℕ) (j : J) (d : MotifEntry.DemandBits a b width j)
    (x : Half P (fun e => Fin (supplyWidths B width payload e) → Bool) j)
    {ls : List (parameterData B).Entry} (hit : (runEntry B hp width payload j d x).1 = some ls) :
    ls.length = repetitions B width := by
  unfold runEntry at hit
  erw [MotifEntry.run_value] at hit
  unfold MotifEntry.describe MotifEntry.labels at hit
  obtain ⟨idx, _, rfl⟩ := Option.map_eq_some_iff.mp hit
  exact List.length_ofFn

end PairSimulation.LocalHistory

namespace PairSimulation.ResidentMapLoop

/-- On a successful loop the list has exactly the sum of the copy counts.
A failing loop keeps the prefix already emitted, bounded by the same sum. -/
theorem labels_length_ofFn {t n : ℕ} (jobs : Fin n → Job t) (copies : Fin n → ℕ)
    (lengths : ∀ i ls, (jobs i).names = some ls → ls.length = copies i) :
    (labels (List.ofFn jobs)).length ≤ ∑ i, copies i ∧
      (passed (List.ofFn jobs) = true → (labels (List.ofFn jobs)).length = ∑ i, copies i) := by
  induction n with
  | zero => simp [labels, passed]
  | succ n ih =>
    obtain ⟨leTail, eqTail⟩ := ih (fun i => jobs i.succ) (fun i => copies i.succ)
      (fun i => lengths i.succ)
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    cases first : (jobs 0).names with
    | none => simp [labels, passed, first]
    | some ls =>
      have head := lengths 0 ls first
      simp only [labels, first, Option.elim_some, List.length_append, head]
      constructor
      · exact Nat.add_le_add_left leTail _
      · intro pass
        have later : passed (List.ofFn fun i => jobs i.succ) = true := by
          simpa [passed, first] using pass
        rw [eqTail later]

end PairSimulation.ResidentMapLoop

namespace PairSimulation.ShrinkRole.MapWitness

open Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel LocalHistory
open MotifBlocks MotifConversion MotifGrid MotifDemandPadding MotifSelector
open CompressorRecords

variable {K : Type*} [Field K] {S : BlockSchedule K} (B : S.Templates)

theorem names_length (arg : EntryInput B.shrink) {ls : List (parameterData B.shrink).Entry}
    (hit : names B arg = some ls) : ls.length = repetitions B.shrink arg.demand :=
  runEntry_length B.shrink demandMass_pos arg.demand arg.payload arg.party _ _ hit

section Entries

variable {n t : ℕ} (args : Fin n → EntryInput B.shrink)
    (index : (parameterData B.shrink).Entry → Fin t) (jobs : Fin n → ResidentMapLoop.Job t)
    (correct : ∀ j, (jobs j).names = (names B (args j)).map (List.map index))

include correct in
/-- On a passed row the degree equals the sum of the repetitions of its
actual entry calls. Every prefix of a rejecting row satisfies the upper bound. -/
theorem row_label_lengths :
    (ResidentMapLoop.labels (List.ofFn jobs)).length ≤ ∑ j, repetitions B.shrink (args j).demand ∧
      (ResidentMapLoop.passed (List.ofFn jobs) = true →
        (ResidentMapLoop.labels (List.ofFn jobs)).length =
          ∑ j, repetitions B.shrink (args j).demand) := by
  apply ResidentMapLoop.labels_length_ofFn jobs
  intro j ls hit
  rw [correct] at hit
  obtain ⟨body, success, rfl⟩ := Option.map_eq_some_iff.mp hit
  rw [List.length_map]
  exact names_length B _ success

include correct in
theorem row_label_max (bound : ℕ) (copyBound : ∀ j, repetitions B.shrink (args j).demand ≤ bound) :
    (ResidentMapLoop.labels (List.ofFn jobs)).length ≤ n * bound := by
  apply (row_label_lengths B args index jobs correct).1.trans
  calc
    _ ≤ ∑ _ : Fin n, bound := Finset.sum_le_sum fun j _ => copyBound j
    _ = _ := by simp

end Entries

section Ordered

variable {a l t : ℕ} (Y : State a (packingLaneBits a l)) (layoutSide : Bool)
    (v : MapResidentRows.Site Y)
/-- Classical decidable equality on the compression state’s base vertices for counting labels
in the ordered resident row. -/
noncomputable local instance : DecidableEq Y.Base := Classical.decEq _
variable (args : Fin (MapResidentRows.order Y layoutSide v).length → EntryInput B.shrink)
    (widths : ∀ j : Fin (MapResidentRows.order Y layoutSide v).length,
      (args j).demand = Y.packingData.shrinkDemandWidths Y.shrinkNumber Y.packingWidth
        (MapResidentRows.entry Y layoutSide v j).1)
    (index : (parameterData B.shrink).Entry → Fin t)
    (jobs : Fin (MapResidentRows.order Y layoutSide v).length → ResidentMapLoop.Job t)
    (correct : ∀ j : Fin (MapResidentRows.order Y layoutSide v).length,
      (jobs j).names = (names B (args j)).map (List.map index))

include Y layoutSide v args widths index jobs correct

set_option maxHeartbeats 1000000 in
-- The demand vector uses a dependent projection from the enumerated resident.
/-- The resident row in the published directory has a linear label budget
in the input width, including inputs that fail at a later occurrence. -/
theorem row_label_budget :
    (ResidentMapLoop.labels (List.ofFn jobs)).length ≤
      MapResidentRows.capacity a * fieldFactor B.shrink * (Y.maxWireWidth + 1) := by
  rw [Nat.mul_assoc, ← MapResidentRows.length_eq Y layoutSide v]
  apply row_label_max B args index jobs correct
  intro j
  rw [widths]
  exact (linear_field_bounds B.shrink _ _ (Y.packingData.shrinkDemandWidths_le
    (State.two_le_packingColors _) (Nat.two_pow_pos _) Y.shrinkNumber Y.packingWidth
    (fun _ => Y.width_le_maxWireWidth _) _)).1

theorem row_label_count_le_square (n : ℕ) (hn : 1 ≤ n) (width : Y.maxWireWidth ≤ n)
    (large : 2 * (MapResidentRows.capacity a * fieldFactor B.shrink) ≤ n)
    (label : Fin t) : (ResidentMapLoop.labels (List.ofFn jobs)).count label ≤ n ^ 2 := by
  let c := MapResidentRows.capacity a * fieldFactor B.shrink
  have bound := row_label_budget B Y layoutSide v args widths index jobs correct
  refine (List.count_le_length (a := label)).trans (bound.trans ?_)
  calc
    c * (Y.maxWireWidth + 1) ≤ c * (2 * n) := Nat.mul_le_mul_left _ (by omega)
    _ = (2 * c) * n := by ring
    _ ≤ n ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ large

end Ordered

section Selected

open CompressorRecords.ShrinkSlots

variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps) {g : ℕ}
    (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (sel : X.ShrinkSelection B.shrink) (v : MapResidentRows.Site X)
/-- Classical decidable equality on the compression state’s base vertices for bounding the
exponents of the selected shrink witness. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _

variable (old : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
      X.packingInputIso.site.symm)
      X.network.Half v)
    (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
local notation "W" => B.shrinkPassWitnesses f hf i rfl X sel v old parent
local notation "side" => selectedLayout X B.shrink sel

set_option maxHeartbeats 2000000 in
-- The kernel witness and the six-party resident subtype use dependent reindexings.
/-- Bound the increment of the actual selected kernel witness in the common
parameter alphabet, at the point where the frontier checks word headroom. -/
theorem selected_exponent_bound (x : (W).Choice) (label : B.Entry) :
    (W).exponents x label ≤ MapResidentRows.capacity (S.degreeExponent i.castSucc) *
      fieldFactor B.shrink * (X.maxWireWidth + 1) := by
  classical
  cases label with
  | inr l => rw [refresh_exponent B f hf i X sel v old parent x l]; exact Nat.zero_le _
  | inl l =>
    rw [exponent_count B f hf i X sel v old parent x l]
    have cardinal : Fintype.card (X.packingData.ResidentMap side v) =
        MapResidentRows.capacity (S.degreeExponent i.castSucc) := by
      rw [Fintype.card_congr (rowEquiv X side v).symm, Fintype.card_fin, MapResidentRows.length_eq]
    calc
      _ ≤ ∑ _ : X.packingData.ResidentMap side v, fieldFactor B.shrink * (X.maxWireWidth + 1) := by
        apply Finset.sum_le_sum
        intro q _
        let I := input B i X sel v old parent x.1 q
        have limit : repetitions B.shrink I.demand ≤ fieldFactor B.shrink * (X.maxWireWidth + 1) :=
          (linear_field_bounds B.shrink _ _ (X.packingData.shrinkDemandWidths_le
            (State.two_le_packingColors _) (Nat.two_pow_pos _) X.shrinkNumber X.packingWidth
            (fun _ => X.width_le_maxWireWidth _) q.val.1)).1
        change ((names B I).getD []).count l ≤ _
        cases got : names B I with
        | none => simp
        | some ls =>
          exact (List.count_le_length (a := l) (l := ls)).trans
            ((names_length B I got).le.trans limit)
      _ = _ := by simp [cardinal, Nat.mul_assoc]

theorem exponent_le_square (x : (W).Choice) (label : B.Entry) {n : ℕ} (hn : 1 ≤ n)
    (width : X.maxWireWidth ≤ n)
    (large : 2 * (MapResidentRows.capacity (S.degreeExponent i.castSucc) *
      fieldFactor B.shrink) ≤ n) :
    (W).exponents x label ≤ n ^ 2 := by
  let c := MapResidentRows.capacity (S.degreeExponent i.castSucc) * fieldFactor B.shrink
  apply (selected_exponent_bound B f hf i X sel v old parent x label).trans
  calc
    c * (X.maxWireWidth + 1) ≤ c * (2 * n) := Nat.mul_le_mul_left _ (by omega)
    _ = (2 * c) * n := by ring
    _ ≤ n ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ large

end Selected

open Filter in
/-- The input-length threshold for all shrinking stages is fixed before
choosing any state, layout, site or branch of the schedule. -/
theorem eventually_row_constants :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ ∀ j : Fin S.steps,
      2 * (MapResidentRows.capacity (S.degreeExponent j.castSucc) * fieldFactor B.shrink) ≤ n := by
  let coeff (j : Fin S.steps) :=
    2 * (MapResidentRows.capacity (S.degreeExponent j.castSucc) * fieldFactor B.shrink)
  filter_upwards [eventually_ge_atTop (max 1 (Finset.univ.sup coeff))] with n hn
  exact ⟨(le_max_left ..).trans hn, fun j =>
    (Finset.le_sup (f := coeff) (Finset.mem_univ j)).trans ((le_max_right ..).trans hn)⟩

end PairSimulation.ShrinkRole.MapWitness

namespace PairSimulation.ShrinkPartyNative

open Compression Compression.PackingData Compression.ShrinkMotif CompressorRecords
open CompressorRecords.ShrinkSlots NetworkKernel

attribute [local irreducible] LocalHistory.Order.restrict LocalHistory.shrinkMotifOrder
  LocalHistory.Order.prod ShrinkCallABI.family

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
    {a b g w t : ℕ} {δ : ℝ} (X : State a (packingLaneBits a g))
    (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ) (sel : X.ShrinkSelection B.shrink)
    (v : MapResidentRows.Site X)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X B.shrink sel
local notation "row" => Fin (LocalHistory.Order.length (MapResidentRows.order X side v))
local notation "motif" => fun j => Prod.fst (MapResidentRows.entry X side v j)
local notation "party" => fun j => Prod.snd (MapResidentRows.entry X side v j)

set_option maxHeartbeats 1500000 in
-- The real party job specializes both halves of the indexed handler family.
/-- Apply the width bound directly to the selected handler family on the
physical party jobs. Work and probe charges do not affect its emitted labels. -/
theorem native_row_label_budget (degree : ℕ) (index : B.Entry → Fin t)
    (calls : ∀ j : row, Job X B.shrink ready sel (motif j) (party j) w)
    (hidden : ∀ j : row, Placed (X.packingData.shrinkInternalOwner side)
      (internalLabel (ShrinkPreparedCall.width B.shrink X sel) side)
      (X.packingData.shrinkPartySite side (motif j) (party j)))
    (work probes : row → ℕ) :
    let inputs := fun j => Job.entryInput B X ready sel (motif j) (party j) (calls j) (hidden j)
    let family := ShrinkCallABI.family B degree a index
    let jobs := List.ofFn fun j => ResidentMapLoop.Job.mk
      (MapHandlerOperand.names family demandMass_pos (inputs j)) (work j) (probes j)
    (ResidentMapLoop.labels jobs).length ≤
      MapResidentRows.capacity a * fieldFactor B.shrink * (X.maxWireWidth + 1) := by
  intro inputs family jobs
  exact ShrinkRole.MapWitness.row_label_budget B X side v inputs (fun _ => rfl) family.ordinal
    (fun j => ⟨MapHandlerOperand.names family demandMass_pos (inputs j), work j, probes j⟩)
    (fun _ => rfl)

end PairSimulation.ShrinkPartyNative

namespace CompressorRecords.PortRefresh.TraversalPlan

open Compression Compression.Refresh Compression.DegreeRefresh NetworkKernel PairSimulation
open MotifConversion MotifDemandPadding MotifSelector LocalHistory RefreshMapOperands

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
    {hist g : ℕ} (order : B.Entry ≃ Fin hist) (X : State S.portExponent (S.portExponent + g))
    (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
      (S.port_bound.connected_and_pos S.port_order).1 B.refresh)
    (v : (X.Base × BitWord g) × Fin (2 ^ S.portExponent))
    (old : X.network.Half (oldSite X v))
    (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
      (S.port_bound.connected_and_pos S.port_order).1 B.refresh S.port_order
      S.degree_bounds.2 choice).network.Half
        (promotedSites v))

/-- The native refresh has one motif call after its diagonal checks. -/
theorem emitted_length {ls : List (Fin hist)} (hit : emitted B order X choice v old new = some ls) :
    ls.length = repetitions B.refresh
      (blockDemandWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) v.1) := by
  unfold emitted at hit
  split at hit
  · obtain ⟨names, success, rfl⟩ := Option.map_eq_some_iff.mp hit
    rw [List.length_map]
    exact runEntry_length B.refresh _ _ _ _ _ _ success
  · contradiction

theorem emitted_length_bound {ls : List (Fin hist)}
    (hit : emitted B order X choice v old new = some ls) :
    ls.length ≤ Fintype.card (Tie (2 ^ S.portExponent)) * X.maxWireWidth := by
  rw [emitted_length B order X choice v old new hit]
  apply term_repetitions_le
  intro e
  unfold blockDemandWidths internalWidth
  split <;> exact X.width_le_maxWireWidth _

end CompressorRecords.PortRefresh.TraversalPlan

end VPVNP
end Computability
end OAI
