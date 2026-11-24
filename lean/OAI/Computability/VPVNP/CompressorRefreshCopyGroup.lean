import OAI.Computability.VPVNP.CompressorRefreshCopyPackets
import OAI.Computability.VPVNP.CompressorRefreshCopyGeometry
import OAI.Computability.VPVNP.CompressorRefreshCopyHeader
import OAI.Computability.VPVNP.CompressorBlockLevelFit
import OAI.Computability.VPVNP.CompressorRecordRefreshLifetime

/-!
# The canonical successor incidence of the selected refresh

The fixed block allocates the temporary output in table zero of the old level.
The six actual copy packets read it and populate the new level's incidence
arrays. Every old record and both levels' published heads survive these copies.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshCopyPackets

open BurstRAM BlockPlanner DescriptorSpace Schedule Compression Compression.Refresh
  Compression.DegreeRefresh
open SourceTransport SourceOnline CopyIncidence PortRefresh
open scoped Fin.CommRing

/-- Exact post-memory, physical footprint, and native charge of the six-copy group. -/
structure CopyResult {w a g : ℕ} (state : State a g) (plan : Allocation.Plan) (layout : Layout)
    (nextLevel : ℕ) (m : Memory w) (rs : List (Report w)) : Prop where
  reports_eq : rs = reports state (plan.output w)
    (packedIncidence layout w nextLevel (state.positions * 2 ^ a)) allColumns m
  stop_before : plan.stop ≤ incidenceStart layout nextLevel
  stop_fits : plan.stop < 2 ^ w
  represents : (packedIncidence layout w nextLevel (state.positions * 2 ^ a)).Represents state
    (after m (eventLog rs))
  read : Reads (fun x => plan.next ≤ x ∧ x < plan.stop) (eventLog rs)
  write : Writes (fun x => incidenceStart layout nextLevel ≤ x ∧
    x < incidenceStart layout nextLevel + 6 * (state.positions * 2 ^ a)) (eventLog rs)
  calls : rs.length = 3 * (Fintype.card state.Base * 2 ^ a) + 3 * (state.positions * 2 ^ a)
  charge : RAMBuckets.cost Report.probes rs = 3 * rs.length

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  {w g : ℕ} (base : BurstRAM.Word w) (positions blocks t : ℕ) (X : State S.portExponent
    (S.portExponent + g))

local notation "s" => RefreshBlockPlan.shape B
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "first" => Script.levelsPerBlock scr * t
local notation "cur" => first + S.steps
local notation "nxt" => first + (S.steps + 1)
local notation "start" => arrayBase L cur
local notation "P" => Allocation.plan X (S.degreeExponent 0) (LevelRecipe.Shape.dH s)
  (LevelRecipe.Shape.ties s) (LevelRecipe.Shape.stride s) start
local notation "T" => Allocation.Plan.output P w
local notation "hC" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "hE" => Nat.two_pow_pos S.expanderExponent
variable (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
local notation "Y" => dyadicRefreshNext X S.graph hE hC B.refresh S.port_order
  (And.right S.degree_bounds) choice
local notation "N" => State.positions Y * 2 ^ (S.degreeExponent 0)
local notation "U" => packedIncidence L w nxt N

/-- Specializes the six-column copy result to the selected refresh state, allocation and next
descriptor level. -/
abbrev Copied (m : Memory w) (rs : List (Report w)) := CopyResult Y P L nxt m rs

section Frame

variable {B base positions blocks t X choice}

theorem Copied.frame {m : Memory w} {rs : List (Report w)} (copied : Copied B base positions
    blocks t X choice m rs)
    (x : ℕ) (away : x < incidenceStart L nxt ∨ incidenceStart L nxt + 6 * (N) ≤ x) :
    after m (eventLog rs) x = m x := after_outside m copied.write (by omega)

/-- The original typed demands, grid coordinates, repetitions and payloads remain
available to the later selected-branch DFS traversal. -/
theorem Copied.stored {m : Memory w} {rs : List (Report w)}
    (copied : Copied B base positions blocks t X choice m rs) {segmentFit}
    (data : Build.Stored X S.graph hE hC B.refresh choice (RefreshBlockPlan.order B) start
      (s).stride segmentFit m) :
    Build.Stored X S.graph hE hC B.refresh choice (RefreshBlockPlan.order B) start
      (s).stride segmentFit
      (after m (eventLog rs)) := by
  apply data.transfer (a₀ := S.degreeExponent 0) le_rfl copied.stop_fits.le
  intro x _ upper
  have before : (P).supply ≤ (P).stop := by
    unfold Allocation.Plan.stop Allocation.Plan.next Allocation.Plan.reverseSlot
      Allocation.Plan.targetPort
    omega
  exact after_outside m copied.write (fun h => (upper.trans_le
    (before.trans copied.stop_before)).not_ge h.1)

end Frame

/-- The old header, canonical successor head bank and physically populated
temporary graph suffice for all six real online launches. The block size
bound places their source and destination in disjoint reserved intervals. -/
theorem group (cap : ℕ) (m : Memory w) (old : IncidenceDirectory w)
    (ht : t < blocks) (size : X.positions ≤ positions) (fit : endAddress L < 2 ^ w)
    (rowsCell : m (pt).rows.val = (directoryRows L : BurstRAM.Word w))
    (pitch : m ((pt).directory - 1).val = (levelWords L : BurstRAM.Word w))
      (clock : scanCap scr 12 ≤ cap)
    (header : RefreshCore.Header (Fintype.card X.Base) g (levelStart L cur) start old m)
    (successor : TraversalHeaders.HeadBank L nxt (N) m) (rep : (T).Represents Y m) :
    ∃ ps : List (Packet scr w), Group scr L base cap
      ((scr).initial.length + t * (scr).block.length + (window B).before.length)
        (directoryRows L) m ps ∧
      ps.map (fun p => p.stage.phase) = (window B).indices ∧
      Copied B base positions blocks t X choice m (ps.flatMap SourceWalk.Packet.reports) := by
  have nextLive : nxt < (L).levels := by
    have h := Nat.mul_le_mul_left (S.steps + 1) ht
    change (S.steps + 1) * t + (S.steps + 1) < 1 + (S.steps + 1) * blocks
    rw [Nat.mul_succ] at h; omega
  let current : Fin (L).levels := ⟨cur, by omega⟩
  let next : Fin (L).levels := ⟨nxt, nextLive⟩
  have endOfPlan := (BlockLevelFit.refresh B base.val positions blocks current rfl X size
    fit).1.next
  have table0 : BlockLevelFit.tableStart L cur 0 = start := by
    simp only [BlockLevelFit.tableStart, Nat.zero_mul, Nat.add_zero]
  change (Allocation.plan X (S.degreeExponent 0) (s).dH (s).ties (s).stride
    (BlockLevelFit.tableStart L cur 0)).stop ≤
    levelStart L ((cur) + 1) at endOfPlan
  rw [table0, show (cur) + 1 = nxt by omega] at endOfPlan
  have separate := endOfPlan.trans (Nat.le_add_right (levelStart L nxt) (levelHeaderWords L))
  have count := dyadicRefreshNext_positions X S.graph hE hC B.refresh S.port_order
    (And.right S.degree_bounds) choice
  have degree := (Finset.le_sup (f := fun j : Fin (S.steps + 1) => 2 ^ S.degreeExponent j)
    (Finset.mem_univ 0)).trans (le_max_right (2 ^ S.portExponent) _)
  have capacity : N ≤ slotCapacity L := Nat.mul_le_mul (count.le.trans size) degree
  have geometry := CopyGeometry.packed X S.graph hE hC B.refresh S.port_order
    (And.right S.degree_bounds) choice
    (s).ties (s).stride L cur next separate fit capacity
  have earlier := levelStart_mono L (show cur ≤ nxt by omega)
  have firstHead := levelStart_mono L (show 0 ≤ nxt from Nat.zero_le _)
  have low := Window.lowCells (A := scr) L base rfl rfl ((levelStart_mono L
    (Nat.zero_le _)).trans_lt fit)
  have headerLength : levelHeaderWords L = 66 := rfl
  have data (mem : Memory w) (retained : ∀ x < incidenceStart L nxt, mem x = m x) (c : Fin 6) :
      Operands B base positions blocks t Y T U mem c := by
    have oldRead := header.keep (fun i hi => retained _ (by unfold incidenceStart; omega))
    have newRead := successor.keep (fun i hi => retained _ (by unfold incidenceStart; omega))
    have pitch' := (retained _ (low.2.trans_le (firstHead.trans (Nat.le_add_right ..)))).trans pitch
    have card := CopyGeometry.base_count X S.graph hE hC B.refresh S.port_order
      (And.right S.degree_bounds) choice
    obtain ⟨stop, bank, supp⟩ := RefreshCopyHeader.operands B X Y start old base positions blocks
      t mem
      oldRead newRead pitch' ht fit card geometry.slots c
    exact ⟨stop, bank, supp⟩
  obtain ⟨ps, packets, phases, hreports⟩ := group_of_operands B base positions blocks t Y T U m
    (incidenceStart L nxt) cap ht fit rowsCell pitch clock (firstHead.trans (Nat.le_add_right ..))
    geometry.roomT geometry.roomU geometry.rowsFit geometry.sourceAbove (fun x h =>
      (geometry.destination x h).1) data
  obtain ⟨run, rep', calls, cost, _, _⟩ := copy_directory Y T U m geometry.regions rep
  have access := run.footprint geometry.roomT geometry.roomU
  refine ⟨ps, packets, phases, ?_⟩
  rw [hreports]
  exact ⟨rfl, separate, endOfPlan.trans_lt ((levelStart_mono L nextLive.le).trans_lt fit), rep',
    fun a v hv => geometry.source _ (access.1 a v hv),
    fun a v hv => geometry.destination _ (access.2 a v hv), calls, cost.trans (congrArg
      (3 * ·) calls.symm)⟩

end CompressorRecords.RefreshCopyPackets

end

end VPVNP
end Computability
end OAI
