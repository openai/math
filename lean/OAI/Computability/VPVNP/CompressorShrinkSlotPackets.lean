import OAI.Computability.VPVNP.CompressorShrinkSlotOrdinals
import OAI.Computability.VPVNP.CompressorSlotCoreAccess
import OAI.Computability.VPVNP.CompressorScriptWindow
import OAI.Computability.VPVNP.CompressorSourceScanned
import OAI.Computability.VPVNP.CompressorShrinkPreparationAccess

/-!
# Checked online packets for a shrinking slot window

The twenty-two source scans retain their global catalog indices, public
banks, tapes and reports. Each report advances its cursor to the next
ordinal and all exclusive stops fit the allocated word. The fixed worker
instruction bound is 49 before adding the online dispatch overhead.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlotPackets

open BurstRAM BlockPlanner DescriptorSpace Schedule SlotLevel ShrinkSlots ShrinkSlotPlan.Scheduled
open scoped Fin.CommRing
open private scanned from OAI.Computability.VPVNP.CompressorShrinkPreparationAccess

variable {A : Script} (P : Plan) (W : Window A (order.map (Stage.visit P)))

/-- Map a scheduled slot-stage index through its script window to the global catalog index. -/
def index (i : Fin order.length) : Fin A.size := W.index (Fin.cast (List.length_map (Stage.visit P)).symm i)

theorem index_visit (i : Fin order.length) : A.visit (index P W i) = order[i.val].visit P := by
  simpa only [index,List.getElem_map,Fin.val_cast] using W.visit (Fin.cast (List.length_map (Stage.visit P)).symm i)

theorem index_worker (i : Fin order.length) : A.catalog (index P W i) = (order[i.val].visit P).worker :=
  congrArg BlockPlanner.Visit.worker (index_visit P W i)

variable {w : ℕ} (s : SlotLevel.Shape) (h : Heads) (chosen : Bool) (splitHead : ℕ) (dest : IncidenceDirectory w)

/-- The online packet for a slot worker, with its global index, physical bank, exclusive stop
and an empty choice stream at each cursor ordinal. -/
def packetVisit (i : Fin order.length) : SourceOnline.Visit A w :=
  let j := order[i.val]
  let v := j.visit P
  SourceOnline.Visit.ofWorker (index P W i) v.worker (index_worker P W i) (v.worker.pcs-1)
    0 (j.limit s : Word w) (j.bank s h chosen splitHead dest ∘ Fin.cast (j.params P))
    (List.replicate (j.limit s) [])

local notation "pkt" => packetVisit P W s h chosen splitHead dest

/-- The embedded catalog visit executes the original source program. -/
theorem runs (i : Fin order.length) (m : Memory w) (rs : List (Report w)) :
    (pkt i).Runs m rs ↔ Source P s h chosen splitHead dest order[i.val] m rs :=
  SourceOnline.Visit.ofWorker_runs _ _ (index_worker P W i) _ _ _ _ _ _ _

theorem fuel_bounds (j : Stage) : 0 < (j.visit P).worker.pcs-1 ∧ (j.visit P).worker.pcs-1 ≤ 49 := by
  cases j with
  | subdivision _ => exact (by decide : 0 < 7 ∧ 7 ≤ 49)
  | roles => exact (by decide : 0 < 26 ∧ 26 ≤ 49)
  | cyclic => exact (by decide : 0 < 19 ∧ 19 ≤ 49)
  | clear => exact (by decide : 0 < 8 ∧ 8 ≤ 49)
  | core p =>
    cases p
    exacts [(by decide : 0 < 49 ∧ 49 ≤ 49), (by decide : 0 < 20 ∧ 20 ≤ 49),
      (by decide : 0 < 23 ∧ 23 ≤ 49), (by decide : 0 < 10 ∧ 10 ≤ 49), (by decide : 0 < 33 ∧ 33 ≤ 49)]
  | output p =>
    cases p
    exacts [(by decide : 0 < 10 ∧ 10 ≤ 49), (by decide : 0 < 28 ∧ 28 ≤ 49),
      (by decide : 0 < 28 ∧ 28 ≤ 49), (by decide : 0 < 43 ∧ 43 ≤ 49)]
  | copy _ => exact (by decide : 0 < 12 ∧ 12 ≤ 49)

/-- The allocated endpoint, counter, sorted-row and incidence arrays bound
every stop, including the strided rectangle traversed by inversion. -/
theorem limit_fit (sp : Build.Space s h splitHead w) (j : Stage) : j.limit s < 2^w := by
  have fit := sp.fit
  unfold finish widthHead inHead outHead inverseBaseHead stopAddress shiftsHead targetsHead
    inverseHead rowsHead at fit
  have rc := sp.roles
  have nc := sp.next
  have sc := sp.subdiv
  have gc := counts_add s
  have ownerBound := Nat.mul_le_mul_right s.newDegree (Nat.le_add_right (owners s) (fields s))
  have siteBound : sites s ≤ owners s := by unfold owners; omega
  cases j with
  | core p => cases p <;> simp only [Stage.limit,SlotLevel.limit] <;> omega
  | output p => cases p <;> simp only [Stage.limit,ShrinkSlots.Recipe.limit] <;> omega
  | copy c => simp only [Stage.limit]; split <;> omega
  | _ => simp only [Stage.limit]; omega

theorem scanned_source (j : Stage) (m : Memory w) (rs : List (Report w))
    (source : Source P s h chosen splitHead dest j m rs) : StageFrame.Scanned 0 (j.limit s) rs := by
  let data := j.bank s h chosen splitHead dest ∘ Fin.cast (j.params P)
  have shape := scanned (j.advance P data) m 0 (j.limit s) rs source
  simpa only [Nat.zero_add] using shape

/-- Check the embedded packet at a single occurrence using its original
worker run and the lower bounds on all of its external accesses. -/
theorem checked_source (i : Fin order.length) (L : DescriptorSpace.Layout) (cap : ℕ)
    (sp : Build.Space s h splitHead w) (capFits : SourceOnline.scanCap A 49 ≤ cap)
    (mem : Memory w) (logs : List (Report w))
    (source : Source P s h chosen splitHead dest order[i.val] mem logs)
    (access : LogAccess (levelStart L 0 ≤ ·) (levelStart L 0 ≤ ·) logs) :
    SourceOnline.Checked A L cap ⟨pkt i,mem,logs⟩ := by
  let j := order[i.val]
  let p : SourceWalk.Packet (SourceOnline.Visit A w) w := ⟨pkt i,mem,logs⟩
  have fuel : 0 < p.stage.fuel ∧ p.stage.fuel ≤ 49 := fuel_bounds P j
  have clocks := SourceOnline.scanCap_clocks (p := p) 49 fuel.2 capFits
  exact SourceOnline.Checked.ofScanned fuel.1 clocks.1 clocks.2 (first := 0) rfl rfl
    (limit_fit s h splitHead sp j) (scanned_source P s h chosen splitHead dest j mem logs source)
    access.1 access.2 (fun _ hx ↦ hx) (fun _ hx ↦ hx)

/-- Embed the entire chronological slot program and check each online packet
using its actual source access bounds above the persistent level base. -/
theorem checked_walk (L : DescriptorSpace.Layout) (cap : ℕ) (sp : Build.Space s h splitHead w)
    (capFits : SourceOnline.scanCap A 49 ≤ cap) (m : Memory w) (rs : List (Report w))
    (walk : SourceWalk (fun j mem logs ↦ Source P s h chosen splitHead dest j mem logs ∧
      LogAccess (levelStart L 0 ≤ ·) (levelStart L 0 ≤ ·) logs) order m rs) :
    SourceWalk (fun v mem logs ↦ v.Runs mem logs ∧ SourceOnline.Checked A L cap ⟨v,mem,logs⟩)
      (List.ofFn pkt) m rs := by
  apply walk.mapAt pkt
  intro i mem logs hs
  exact ⟨(runs P W s h chosen splitHead dest i mem logs).2 hs.1,
    checked_source P W s h chosen splitHead dest i L cap sp capFits mem logs hs.1 hs.2⟩

end CompressorRecords.ShrinkSlotPackets

end VPVNP
end Computability
end OAI
