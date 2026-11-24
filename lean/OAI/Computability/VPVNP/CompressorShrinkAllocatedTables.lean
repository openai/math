import OAI.Computability.VPVNP.CompressorShrinkSelectedOutput
import OAI.Computability.VPVNP.CompressorBlockABSliceRun
import OAI.Computability.VPVNP.CompressorScheduledSliceRates

/-! # Separate AB, surviving-width and ordered-slot tables in the physical block

The block calendar builds the AB intersections before its four surviving
role scans. Each table has its own advised base address. The incidence
directory, endpoint lists, and both kinds of interval descriptors are
readable in the same final memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkOutput

open Compression Compression.PackingData Compression.ShrinkMotif MotifBlocks MotifGrid
open BurstRAM PhaseRecipe ShrinkSliceSweep ShrinkBlockInputs SlotLevel ShrinkSlots
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} {δ : ℝ} (X : State (a i) (packingLaneBits (a i) g))
variable (ready : Ready (2^(a i)) (Shrink.colors (a i)) (2^(b i)) δ) (sel : SelectedScore.Selection B X)
variable (term stride abs : Word w) (T : IncidenceDirectory w) (start : ℕ)

local notation "sh" => levelShape (b := b i) X
local notation "role" => SelectedArena.roleBase X term stride
local notation "keepEnd" => SelectedFinish.stop X term stride
local notation "ns" => ShrinkBundlePlan.thickCount (a i)
local notation "nt" => ShrinkBundlePlan.cap (a i)
local notation "z" => ShrinkInput.plan X start
local notation "sitesOrd" => Shrink.packedIndex (a := a i) (g := g) X.baseIndex
local notation "thick" => ShrinkInput.thickBank X T start
local notation "cd" => ShrinkInput.cdBank X T start
local notation "pieces" => ShrinkInput.piecesBank X T start
local notation "chosenSide" => SelectedFinish.chosen B X sel
local notation "bankAt" => splitBank (b := b i) X B.shrink sel term stride.val role

theorem old_bounds :
    term.val+motifCount X*stride.val ≤ keepEnd ∧ role+4*absoluteCount X ≤ keepEnd ∧
      SelectedArena.origin X term stride+2 < keepEnd := by
  have hc : motifCount X = SelectedArena.motifs X :=
    ((Fintype.card_congr (ShrinkMotifOrder.stateNumber X)).trans (Fintype.card_fin _)).symm
  unfold SelectedFinish.stop SelectedFinish.rowStart SelectedFinish.countStart
    SelectedArena.endAddr SelectedArena.roleBase SelectedArena.placementBase SelectedArena.origin
  rw [hc]
  unfold absoluteCount
  omega

/-- The requested width-table base is used exactly when the preceding
resident fields fit below it. -/
theorem width_at_eq (width : ℕ) (low : keepEnd ≤ width) : widthBase X term.val stride.val role width = width := by
  have h := old_bounds i X term stride
  unfold widthBase
  rw [max_eq_right (h.2.1.trans low),max_eq_right (h.1.trans low)]

/-- Readbacks inherited by the AB and surviving-width workers from the
term, placement and preimage passes. -/
structure Resident (width : ℕ) (mem : Memory w) : Prop where
  demand : DemandWidths.Stored X.packingData sitesOrd X.packingWidth X.shrinkOrder X.shrinkNumber thick cd pieces mem
  directory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber abs mem
  terms : Terms X.packingData X.shrinkNumber sitesOrd (bankAt width) B.shrink X.packingWidth sel mem
  roles : DemandRAM.RoleColumns X chosenSide role mem
  chosen : mem (SelectedArena.origin X term stride+2) = ((chosenSide).toNat : Word w)
  preimages : ShrinkPreimages.Directory X chosenSide (SelectedFinish.counts X term stride) (SelectedFinish.rows X term stride) mem

variable {F : DescriptorSpace.Shape} {origin abArena : Expr} {pub : Fin 5 → Word w} {state : Word w} {ref : Memory w}

/-- Every assigned bundle's final bank stores the intersections between its old thick fields
and new AB pieces in the prescribed orders. -/
abbrev ABFields (first : ℕ) (out : Memory w) :=
  ∀ bundle, IndexedStarts.Stored (ShrinkABSliceTable.bank first ns nt (BundleLists.portIndex sitesOrd bundle).val)
    (ShrinkSliceArrays.thickWidths X.packingData X.shrinkOrder X.packingWidth bundle)
    (ShrinkSliceArrays.abWidths X.packingData X.shrinkNumber X.packingWidth bundle) out

/-- The successive reports of the AB phase and both output phases. -/
structure TablesRun (w : ℕ) where
  /-- Reports emitted by the initial AB intersection scans before construction of the surviving
  and ordered-slot tables. -/
  intersections : List (Report w)
  /-- The remaining shrinking passes after the AB intersections, including their final memory. -/
  remainder : Passes w

/-- Replay the intersection reports on the input memory to obtain the starting memory of the
remaining passes. -/
def TablesRun.postAB (r : TablesRun w) (mem : Memory w) := after mem (eventLog r.intersections)
/-- The complete report sequence, with the AB intersection scans followed by the remaining
table-building passes. -/
def TablesRun.reports (r : TablesRun w) := r.intersections++r.remainder.reports
/-- The final memory of the remaining passes after the AB, surviving-width and ordered-slot
tables have been built. -/
def TablesRun.final (r : TablesRun w) := r.remainder.final

/-- The chronological AB and remaining passes build all three tables, preserve memory outside
the AB bank during its construction, and replay to the claimed final memory. -/
structure CompleteTables (I : ShrinkABSliceRecipe.Inputs) (pub : Fin 5 → Word w) (state : Word w) (ref : Memory w)
    (first width slotStart cap : ℕ) (mem : Memory w) (r : TablesRun w) : Prop where
  abRun : SourceWalk (ShrinkABSliceRecipe.Source I pub state ref (z).B cap) (ShrinkABSliceRecipe.phases ns nt)
    mem r.intersections
  abFrame : ∀ x, x < first ∨ first+(z).B*IndexedStarts.capacity ns nt ≤ x → r.postAB mem x = mem x
  remainder : Complete B X ready sel term stride abs cap (r.postAB mem) r.remainder width slotStart
  abFields : ABFields i X first r.final
  replay : after mem (eventLog r.reports) = r.final

/-- The number of calls and probes includes the native AB work, all four
role scans, and the complete ordered-slot passes. -/
theorem CompleteTables.cost {I : ShrinkABSliceRecipe.Inputs} {first width slotStart cap : ℕ} {mem : Memory w}
    {r : TablesRun w} (h : CompleteTables B i X ready sel term stride abs start I pub state ref first width slotStart cap mem r) :
    RAMBuckets.cost Report.probes r.reports ≤ (z).B*(2*(ns+nt)+16*(ns*nt)) +
      (18*(motifCount X*(bankAt width).stride)+slotProbes sh) := by
  have ab := ScheduledRates.scheduledABCounts I pub state ref h.abRun
  exact (RAMBuckets.cost_append Report.probes r.intersections r.remainder.reports).le.trans
    (Nat.add_le_add ab.2.1 h.remainder.probes.le)

set_option maxHeartbeats 2400000 in
/-- Run the actual AB source visits, then the native surviving-role and slot
workers. The source memory may already contain the hidden history records.
Only established readbacks of its existing columns and selected terms are
needed. All three output tables are built from those inputs. -/
theorem withAB (first width slotStart cap : ℕ) (mem : Memory w)
    (level : ShrinkBundlePlan.Reads X F i.val origin pub state ref start T)
    (arena : abArena.eval pub state ref = (first : Word w))
    (termRoom : ShrinkInput.termEnd X start stride.val < 2^w) (fresh : ShrinkInput.stop X start ≤ first)
    (widthRoom : nt*X.maxWireWidth < 2^w)
    (abAfter : keepEnd ≤ first) (widthAfter : first+(z).B*IndexedStarts.capacity ns nt ≤ width)
    (slotAfter : (bankAt width).last ≤ slotStart) (slotRoom : finish sh (heads sh role slotStart) < 2^w)
    (wide : 10 ≤ stride.val) (hw : FitsWords (b := b i) X B.shrink term stride.val role width)
    (absBefore : abs.val+motifCount X ≤ keepEnd)
    (resident : Resident B i X sel term stride abs T start width mem)
    (abFuel : 95 ≤ cap) (sweepFuel : SurvivingNative.ops.length < cap) :
    ∃ r, CompleteTables B i X ready sel term stride abs start (BlockSlices.abInputs i origin abArena) pub state ref
      first width slotStart cap mem r := by
  have lower : keepEnd ≤ width := abAfter.trans ((Nat.le_add_right first _).trans widthAfter)
  have we := width_at_eq i X term stride width lower
  have fit := fits X B.shrink sel term stride.val role width ready wide hw.room
  have widthFit : width < 2^w := we ▸ (width_le_slots (b := b i) X term stride.val role width).trans_lt
    ((slots_le_stop X term stride.val role width).trans_lt hw.room)
  let abEnd := first+(z).B*IndexedStarts.capacity ns nt
  have abRoom : abEnd < 2^w := widthAfter.trans_lt widthFit
  obtain ⟨rows,walk,abFields,frame⟩ := BlockSlices.ab_run i X T start mem resident.demand level arena termRoom fresh abRoom widthRoom cap abFuel
  let mid := after mem (eventLog rows)
  have old (x : ℕ) (hx : x < keepEnd) : mid x = mem x := frame x (.inl (hx.trans_le abAfter))
  have hb := old_bounds i X term stride
  have roleCopy : DemandRAM.RoleColumns X chosenSide role mid := by
    have keep (arc) (j : ℕ) (hj : j < 4) : mid (role+4*(DemandRAM.absoluteIndex X arc).val+j) = mem (role+4*(DemandRAM.absoluteIndex X arc).val+j) := by
      apply old
      have hi := (DemandRAM.absoluteIndex X arc).isLt
      change (DemandRAM.absoluteIndex X arc).val < absoluteCount X at hi
      omega
    constructor
    · intro arc; rw [keep arc 3 (by decide)]; exact resident.roles.cd arc
    · intro arc r; rw [keep arc (SlotOwners.roleOffset r) (by cases r <;> decide)]; exact resident.roles.packed arc r
  have termsCopy : Terms X.packingData X.shrinkNumber sitesOrd (bankAt width) B.shrink X.packingWidth sel mid := by
    apply terms_after B.shrink X term stride.val _ (sh).subdivisions sel mem mid resident.terms
    intro j q hq b
    have hd : b.val ≤ term.val+j.val*stride.val := Nat.mod_le ..
    have hi := Nat.mul_le_mul_right stride.val j.isLt
    rw [Nat.succ_mul] at hi
    change j.val*stride.val+stride.val ≤ motifCount X*stride.val at hi
    exact old _ ((show b.val+q < term.val+motifCount X*stride.val by omega).trans_le hb.1)
  have ids : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber abs mid := by
    intro j
    exact (congrArg Fin.val (old _ ((Nat.add_lt_add_left j.isLt _).trans_le absBefore))).trans (resident.directory j)
  obtain ⟨passes,done⟩ := build_at B X ready sel term stride abs mid width slotStart lower wide hw slotAfter slotRoom
    absBefore ids termsCopy roleCopy ((old _ hb.2.2).trans resident.chosen) (preimages_retained X term stride resident.preimages old) cap sweepFuel
  let r : TablesRun w := ⟨rows,passes⟩
  refine ⟨r,⟨walk,frame,done,?_,?_⟩⟩
  · intro bundle
    let ix := BundleLists.portIndex sitesOrd bundle
    let A := BlockSlices.ab_layout i X T start termRoom fresh abRoom
    let oldRow := ShrinkSliceArrays.thickWidths X.packingData X.shrinkOrder X.packingWidth bundle
    let newRow := ShrinkSliceArrays.abWidths X.packingData X.shrinkNumber X.packingWidth bundle
    have olen : oldRow.length = ns := List.length_ofFn
    have nlen : newRow.length = nt := List.length_ofFn
    have room := ShrinkABSliceTable.space A ix
    have stored := abFields bundle
    apply stored.transfer (input := ShrinkABSliceTable.columns thick pieces ix.val)
    · rwa [olen,nlen]
    · intro x _ hx
      have hv := ShrinkABSliceTable.bank_val A ix
      have hi := Nat.mul_le_mul_right (IndexedStarts.capacity ns nt) ix.isLt
      rw [Nat.succ_mul] at hi
      change ix.val*IndexedStarts.capacity ns nt+IndexedStarts.capacity ns nt ≤ (z).B*IndexedStarts.capacity ns nt at hi
      change x < (ShrinkABSliceTable.bank first ns nt ix.val : Word w).val+IndexedStarts.capacity oldRow.length newRow.length at hx
      rw [olen,nlen,hv] at hx
      apply done.construction.frame x (.inl ?_)
      rw [we]
      omega
  · exact (show after mem (eventLog (rows++passes.reports)) = after mid (eventLog passes.reports) by
      simp only [mid,after,eventLog,List.flatMap_append,List.foldl_append]).trans done.replay

end CompressorRecords.ShrinkOutput

end

end VPVNP
end Computability
end OAI
