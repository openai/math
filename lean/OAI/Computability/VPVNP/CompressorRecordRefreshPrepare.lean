import OAI.Computability.VPVNP.CompressorRecordRefreshDemandScan
import OAI.Computability.VPVNP.CompressorRecordRefreshInputs

/-!
# Preparing the external fields and internal demands of a refresh

The initial state is the shared six-column incidence directory. The three external passes
produce both ends of every segment. The fixed ordered ties then copy the appropriate
outgoing or incoming width into a contiguous demand record at each port block. No term
selection or payload assignment precedes this construction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh

open BurstRAM PrimedStackRAM Compression Compression.Refresh Compression.DegreeRefresh RefreshRAM NewSlots

variable {a g bits t : ℕ} (X : State a (a+g)) (T : IncidenceDirectory bits)
  (q : Fin 8 → BurstRAM.Word bits) (out : BurstRAM.Word bits) (ties : Fin t ≃ Tie (2^a))

local notation "O" => sites (D := 2^a) X.baseIndex (bitWordFinEquiv g)
local notation "V" => Fintype.card X.Base
local notation "B" => V * 2^g
local notation "N" => V * 2^a * 2^g
local notation "S" => N * 2^a

/-- The directory fields needed after the demand scan, including both physical endpoints
of every segment and the individual old width at each end. -/
structure SegmentFields (fit : S ≤ 2^bits) (m : Memory bits) : Prop where
  target : ∀ b, (cell q m 2 (bundleWord O fit b)).val = (O (bundleTarget (splitSlots X) b)).val
  total : ∀ b, (cell q m 4 (bundleWord O fit b)).val = ∑ j, bundleWidths (bitWordFinEquiv a) (splitWidths X) b j
  segments : ∀ e : DyadicArc X.Base (BitWord g) a,
    let i := idWord O fit e
    let j := idWord O fit (oldPortMatching (splitSlots X) (bitWordFinEquiv a) e)
    let r := outgoingRecord (splitSlots X) (bitWordFinEquiv a) (splitWidths X) e
    (cell q m 1 i).val = r.width ∧ (cell q m 5 i).val = r.offset ∧
      (cell q m 6 j).val = r.offset ∧ (cell q m 7 j).val = r.width

/-- Preserve the segment data across writes in other level arrays. -/
theorem SegmentFields.transfer {fit : S ≤ 2^bits} {m m' : Memory bits} (data : SegmentFields X q fit m)
    (frame : ∀ c : Fin 8, c ≠ 0 → ∀ i : BurstRAM.Word bits, i.val < S → cell q m' c i = cell q m c i) :
    SegmentFields X q fit m' := by
  have bn (b : (X.Base × BitWord g) × Fin (2^a)) : (bundleWord O fit b).val < S :=
    (O b).isLt.trans_le (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a))
  constructor
  · intro b; rw [frame 2 (by decide) _ (bn b)]; exact data.target b
  · intro b; rw [frame 4 (by decide) _ (bn b)]; exact data.total b
  · intro e
    dsimp only
    have h (c : Fin 8) (hc : c ≠ 0) (a) := frame c hc (idWord O fit a) (numbered O a).isLt
    simp only [h 1 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
    exact data.segments e

/-- A demand row lies outside the seven segment arrays so all segment descriptors remain
available for the local kernel, even after copying the dense internal demand vector. -/
def demandApart : Prop := ∀ c : Fin 8, c ≠ 0 → ∀ i : BurstRAM.Word bits, i.val < S →
  (q c + i).val < out.val ∨ out.val+B*t ≤ (q c+i).val

/-- Four native passes in their shared-memory execution order. -/
def PrepareRun (lanes : BurstRAM.Word bits) (fit : S ≤ 2^bits)
    (m m' : Memory bits) (reports : List (Report bits)) : Prop :=
  ∃ rg rd re ds,
    ExternalReports X (IncidenceDirectory.baseOrder X) q lanes T.width T.baseOut T.shift m fit rg rd re ∧
    let ext := after (after (after m (eventLog rg)) (eventLog rd)) (eventLog re)
    DemandScan.Runs (DemandScan.words (r := 2^g) ties q out) B (List.finRange t) ext ds ∧
      m' = after ext (eventLog ds) ∧ reports = (rg ++ rd ++ re) ++ ds

/-- From an existing incidence directory to all numerical inputs of the block term tests.
The same output memory also retains all external widths, endpoint offsets and bundle targets. -/
theorem prepare_demands (m : Memory bits) (rep : T.Represents X m) (lanes : BurstRAM.Word bits)
    (degree : (q 0).val = 2^a) (residual : lanes.val = 2^g) (regions : Regions q S)
    (dirLayout : BundleDirectory.Layout (directoryWords q lanes T.baseOut T.shift) (V*2^a) (2^g))
    (wireApart : RefreshGather.SourcesDisjoint (gatherWords q lanes T.width) S)
    (baseApart : baseOutsideGather X (IncidenceDirectory.baseOrder X) q T.baseOut T.shift)
    (widthRoom : ∀ b, (∑ j, bundleWidths (bitWordFinEquiv a) (splitWidths X) b j) < 2^bits)
    (demandRoom : out.val+B*t ≤ 2^bits) (apart : demandApart (t := t) X q out) :
    ∃ rs m', PrepareRun X T q out ties lanes regions.fits m m' rs ∧ SegmentFields X q regions.fits m' ∧
      (∀ s, DemandPreparation.demandAt ties (DemandScan.rowBase X t out s) m' =
        blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) s) ∧
      (∀ addr, outsideLevel q S addr → (addr < out.val ∨ out.val+B*t ≤ addr) → m' addr = m addr) ∧
      RAMBuckets.cost Report.probes rs = 6*N + 12*S + 3*B*t := by
  obtain ⟨rg,rd,re,extReports⟩ := IncidenceDirectory.Represents.external_execution X T m rep q lanes degree residual
    regions dirLayout wireApart baseApart widthRoom
  have ⟨_,_,_,cost,done,frame,totals,rows⟩ := extReports
  let ext := after (after (after m (eventLog rg)) (eventLog rd)) (eventLog re)
  let A := graphInput (bits := bits) (splitSlots X) O (splitWidths X)
  have T' : Directory (splitSlots X) O (splitWidths X) q A regions.fits :=
    graphInput_directory (splitSlots X) O (splitWidths X) q degree widthRoom
  have atEnd : AtCursor q S A ext S := done
  have extData : SegmentFields X q regions.fits ext := by
    refine ⟨fun b => ?_,totals,fun e => ?_⟩
    · exact (congrArg Fin.val (atEnd.target _ (bundleWord_live O q (fit := regions.fits) degree b))).trans (T'.target b)
    · exact ⟨(congrArg Fin.val (atEnd.old _ (numbered O e).isLt)).trans (T'.old e), rows e⟩
  have ap : DemandScan.Apart (t := t) X q out := fun c hc => apart c (by rcases hc with rfl | rfl <;> decide)
  obtain ⟨ds,runD,demand,frameD,costD⟩ := DemandScan.demand_table ext X ties q out regions.fits
    (residual ▸ lanes.isLt) demandRoom ap A T' atEnd (fun e => (rows e).2.2)
  let m' := after ext (eventLog ds)
  refine ⟨(rg ++ rd ++ re) ++ ds, m', ⟨rg,rd,re,ds,extReports,runD,rfl,rfl⟩,
    extData.transfer X q (fun c hc i hi => frameD _ (apart c hc i hi)), demand,
    fun addr he hd => (frameD addr hd).trans (frame addr he), ?_⟩
  exact (RAMBuckets.cost_append Report.probes _ _).trans (congrArg₂ (· + ·) cost costD)

end CompressorRecords.PortRefresh

end VPVNP
end Computability
end OAI
