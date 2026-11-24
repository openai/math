import OAI.Computability.VPVNP.CompressorShrinkAllocatedTables
import OAI.Computability.VPVNP.CompressorShrinkSlotWindow
import OAI.Computability.VPVNP.CompressorScheduledSlotRates
import OAI.Computability.VPVNP.CompressorPublishedHeadWindows
import OAI.Computability.VPVNP.CompressorShrinkLevelSpace

/-! # Tapes and traffic of the three shrinking output windows

The native AB, surviving-width, ordered-slot and canonical-copy reports all
consume empty tapes. We count the calls of each scan and include the actual
copy reports in the bound per incoming wire position. The same statements
hold for the packet choices whenever the packets replay these reports.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkScheduledCharges

open BurstRAM Compression ShrinkBlockInputs ShrinkOutput ShrinkSliceSweep
open SlotLevel ShrinkSlots ShrinkSlotPlan.Scheduled
open scoped Classical Fin.CommRing
open private motif_le packed_le from OAI.Computability.VPVNP.CompressorShrinkLevelSpace

private theorem walk_tapes {J : Type*} {w : ℕ} {run : J → Memory w → List (Report w) → Prop}
    {js : List J} {mem : Memory w} {rs : List (Report w)} (count : J → ℕ)
    (walk : SourceWalk run js mem rs)
    (one : ∀ j m log, run j m log → branchPaths log = List.replicate (count j) []) :
    branchPaths rs = List.replicate ((js.map count).sum) [] := by
  induction walk with
  | done => rfl
  | @next j js m head tail h _ ih =>
    rw [branchPaths,List.map_append,← branchPaths,← branchPaths,one j m head h,ih,
      List.map_cons,List.sum_cons,List.replicate_add]

/-- Incoming positions pay for the AB and width rectangles, and for the
ordered-slot scans and their physical transfers. All three rates depend
only on the fixed degrees and the subdivisions of the template. -/
def rate (a b : ℕ) :=
  let d := 2^a
  let q := ShrinkBundlePlan.cap a
  let t := ShrinkBundlePlan.thickCount a
  let u := ShrinkLevelSpace.subdivisionSum a b
  let s : Shape := ⟨1,1,1,d,Shrink.colors a,Compression.ShrinkMotif.subdivisions d (Shrink.colors a) (2^b),2^b⟩
  d*(2*(t+q)+16*(t*q)) + 18*(d*q)*u + ScheduledRates.slotRate s

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} {δ : ℝ} (X : State (a i) (packingLaneBits (a i) g))
variable (ready : ShrinkMotif.Ready (2^(a i)) (Shrink.colors (a i)) (2^(b i)) δ) (sel : SelectedScore.Selection B X)
variable (term stride abs : Word w) (start : ℕ) {I : ShrinkABSliceRecipe.Inputs}
variable {pub : Fin 5 → Word w} {st : Word w} {ref m : Memory w} {first cap : ℕ} (width slotStart : ℕ)
variable (dst : IncidenceDirectory w) (r : TablesRun w)

local notation "sh" => levelShape (b := b i) X
local notation "role" => SelectedArena.roleBase X term stride
local notation "bank" => splitBank (b := b i) X B.shrink sel term (Fin.val stride) role width
local notation "slotHead" => heads sh role slotStart
local notation "Y" => X.shrinkNext B.shrink ready sel
local notation "src" => directory sh slotHead w
local notation "native" => r.remainder.slots
local notation "raw" => r.remainder.postWidths
local notation "copies" => CopyIncidence.reports Y src dst CopyIncidence.allColumns (after raw (eventLog (Build.Construction.all native)))
local notation "bs" => ShrinkRankSpace.Shape.B (ShrinkInput.plan X start)
local notation "ns" => ShrinkBundlePlan.thickCount (a i)
local notation "nt" => ShrinkBundlePlan.cap (a i)
local notation "nAB" => bs*(ns+nt+2*(ns*nt))
local notation "nWidth" => motifCount X*Allocation.stride bank
local notation "nSlot" => List.sum (List.map (Stage.limit sh) constructionOrder)
local notation "nCopy" => 3*(Fintype.card (State.Base Y)*2^(b i))+3*(State.positions Y*2^(b i))
local notation "allLogs" => r.reports++copies

/-- Counts, costs and choice tapes for the four report lists in Parts 6–8. -/
structure Accounted : Prop where
  abCount : r.intersections.length = nAB
  widthCount : r.remainder.widthRows.flatten.length = nWidth
  slotCount : (native).all.length = nSlot
  copyCount : (copies).length = nCopy
  abTapes : branchPaths r.intersections = List.replicate nAB []
  widthTapes : branchPaths r.remainder.widthRows.flatten = List.replicate nWidth []
  slotTapes : branchPaths (native).all = List.replicate nSlot []
  copyTapes : branchPaths copies = List.replicate nCopy []
  abCost : RAMBuckets.cost Report.probes r.intersections ≤ bs*(2*(ns+nt)+16*(ns*nt))
  widthCost : RAMBuckets.cost Report.probes r.remainder.widthRows.flatten = 18*nWidth
  slotCost : RAMBuckets.cost Report.probes (native).all = slotProbes sh
  copyCost : RAMBuckets.cost Report.probes copies = 9*(Fintype.card (State.Base Y)*2^(b i))+9*(State.positions Y*2^(b i))
  linear : RAMBuckets.cost Report.probes allLogs ≤ X.positions*rate (a i) (b i)

set_option maxHeartbeats 1400000 in
/-- Account for the reports of a completed three-table run and the six copies
which follow it in the ordered-slot window. -/
theorem accounted (run : CompleteTables B i X ready sel term stride abs start I pub st ref first width slotStart cap m r) :
    Accounted B i X ready sel term stride start width slotStart dst r := by
  have ab := ScheduledRates.scheduledABCounts I pub st ref run.abRun
  have abTapes := walk_tapes (fun _ ↦ bs) run.abRun (fun _ _ _ h ↦ ((runSegment_iff ..).mp h).2.2)
  have abNumber : ((ShrinkABSliceRecipe.phases ns nt).map (fun _ ↦ bs)).sum = nAB := by
    have eq := congrArg List.length abTapes
    simpa only [branchPaths,List.length_map,List.length_replicate,ab.1] using eq.symm
  rw [abNumber] at abTapes
  have wc := run.remainder.sweep.calls
  have widthBits : branchPaths r.remainder.widthRows.flatten = List.replicate nWidth [] := by
    rw [← wc]
    apply List.eq_replicate_iff.mpr
    refine ⟨List.length_map _,?_⟩
    intro tape ht
    obtain ⟨rep,hr,rfl⟩ := List.mem_map.mp ht
    obtain ⟨_,_,site⟩ := run.remainder.sweep.sites hr
    exact site.bits
  have slot := run.remainder.construction
  have phases := construction_sources (ShrinkSlotCalendar.plan B i) sh slotHead (selectedLayout X B.shrink sel)
    (bank).widthBase dst native raw slot.slots
  have slotTapes := walk_tapes (Stage.limit sh) phases (fun _ _ _ h ↦ ((runSegment_iff ..).mp h).2.2)
  have slotCount : (native).all.length = nSlot := by
    simpa only [branchPaths,List.length_map,List.length_replicate] using congrArg List.length slotTapes
  have cp := ScheduledRates.copyColumns Y src dst (after raw (eventLog (Build.Construction.all native)))
  have copyBits : branchPaths copies = List.replicate nCopy [] := by
    apply List.eq_replicate_iff.mpr
    refine ⟨(List.length_map _).trans cp.2.1,?_⟩
    intro tape ht
    obtain ⟨rep,hr,rfl⟩ := List.mem_map.mp ht
    exact (CopyIncidence.reports_work Y src dst CopyIncidence.allColumns _).2.2 rep hr |>.2.2
  have widthCost : RAMBuckets.cost Report.probes r.remainder.widthRows.flatten = 18*nWidth := by
    have c := run.remainder.probes
    rw [Passes.reports,RAMBuckets.cost_append,← slot.probes] at c
    exact Nat.add_right_cancel c
  refine ⟨ab.1,wc,slotCount,cp.2.1,abTapes,widthBits,slotTapes,copyBits,ab.2.1,widthCost,
    slot.probes,cp.2.2.1,?_⟩
  have slotTotal := (ScheduledRates.selectedSlotProgram X B.shrink ready sel slotHead (bank).widthBase
    dst raw native slot.slots).2.1
  rw [Build.Construction.final_eq] at slotTotal
  let d := 2^(a i)
  let u := ShrinkLevelSpace.subdivisionSum (a i) (b i)
  let abWeight := 2*(ns+nt)+16*(ns*nt)
  have bFit : bs ≤ X.positions*d := Nat.mul_le_mul_right d (packed_le X)
  have mFit : motifCount X ≤ X.positions*(d*nt) := motif_le X
  have cAB := ab.2.1.trans (Nat.mul_le_mul_right abWeight bFit)
  have cWidth : RAMBuckets.cost Report.probes r.remainder.widthRows.flatten ≤ 18*((X.positions*(d*nt))*u) :=
    widthCost.le.trans (Nat.mul_le_mul_left 18 (Nat.mul_le_mul_right u mFit))
  change RAMBuckets.cost Report.probes ((r.intersections++(r.remainder.widthRows.flatten++(native).all))++copies) ≤
    X.positions*(d*abWeight+18*(d*nt)*u+ScheduledRates.slotRate sh)
  rw [List.append_assoc,List.append_assoc,RAMBuckets.cost_append,RAMBuckets.cost_append]
  calc
    _ ≤ (X.positions*d)*abWeight+(18*((X.positions*(d*nt))*u)+X.positions*ScheduledRates.slotRate sh) :=
      Nat.add_le_add cAB (Nat.add_le_add cWidth slotTotal)
    _ = _ := by ring

/-- The AB intersection probes depend on the widths. Once that observed charge
is fixed, the remaining three scans have the following exact charge. -/
theorem Accounted.exact_cost (h : Accounted B i X ready sel term stride start width slotStart dst r) :
    RAMBuckets.cost Report.probes allLogs = RAMBuckets.cost Report.probes r.intersections +
      (18*nWidth + slotProbes sh) + (9*(Fintype.card (State.Base Y)*2^(b i)) + 9*(State.positions Y*2^(b i))) := by
  simp only [TablesRun.reports,Passes.reports,RAMBuckets.cost_append,h.widthCost,h.slotCost,h.copyCost]

/-- The actual packet tapes and their source charge for the concatenation of
all three windows. The only input about the packets is their verified native
chronology and the equality of the four flattened report lists. -/
theorem Accounted.packets (h : Accounted B i X ready sel term stride start width slotStart dst r)
    {A : BlockPlanner.Script} (input : Memory w) (ps : List (SourceOnline.Packet A w))
    (chron : SourceWalk.Chronological SourceOnline.Visit.Runs input ps)
    (reports : ps.flatMap SourceWalk.Packet.reports = allLogs) :
    ps.flatMap (fun p => p.stage.choices) = List.replicate (nAB+nWidth+nSlot+nCopy) [] ∧
      RAMBuckets.cost Report.probes (ps.flatMap SourceWalk.Packet.reports) ≤ X.positions*rate (a i) (b i) := by
  rw [PublishedHeads.chronological_tapes input ps chron,reports]
  refine ⟨?_,h.linear⟩
  have join (xs ys : List (Report w)) : branchPaths (xs++ys) = branchPaths xs++branchPaths ys := List.map_append
  simp only [TablesRun.reports,Passes.reports,join,h.abTapes,h.widthTapes,h.slotTapes,h.copyTapes]
  simp only [List.replicate_add,List.append_assoc]

end CompressorRecords.ShrinkScheduledCharges

end

end VPVNP
end Computability
end OAI
