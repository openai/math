import OAI.Hierarchy.TraceAdmissionRecovery
import OAI.ThreeFlat.Diagonal.TraceNodeBankScale
import OAI.Hierarchy.TraceSeedVisit

namespace OAI
/-! # Uniform scalar room for the observed seed and every selected archive -/
namespace Hierarchy.TraceAdmission
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM.NavigationNodeRows NodePublication Computability.VPVNP.BurstRAM TraceDistribution Filter
variable {F : Type} [Field F] (B : Block F)

theorem eventual_recovery_geometry_at {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop,∀ {k : ℕ} (_axis : k+1=u w+1-w/2)
      (_fit : B.blockCharge*s w≤k+1)
      (a : Archive) (β : ℕ) (_placed : ArchivePlacement a β w)
      (_alph : a.K=B.alphabetCap) (_de : a.initialDegree=2^B.exponent 0)
      (_ax : a.axes=k+1) (_lanes : a.remainingLanes=2^(k+1)) (cur : Word (64*w))
      (_ptr : cur.val=a.control),
      let P:=B.repeat (s w)
      let rem:=k+1-P.charge
      let ops:=P.directory rem (k+1)
      let stop:=finish a.K ops a.cursor
      2*a.initialDegree≤directoryCap B ∧ stop.header≤a.initialRecords ∧
        a.metadataEnd≤a.cursor.heap ∧ a.cursor.heap≤cur.val ∧ stop.header≤a.cursor.heap ∧
        a.cursor.node+a.seedLayer.count+(ops.map Stage.nodes).sum+(ops.map successors).sum≤2^(64*w) ∧
        stop.heap≤a.control+64 := by
  filter_upwards [eventual_node_limits B scale,TraceSeedWriter.eventual_seed_arrays B scale,
    eventual_iteration_limits B scale,eventually_ge_atTop 7] with w node arrays iterator hw
  intro k _axis _fit a β _placed _alph _de _ax _lanes cur _ptr P rem ops stop
  have fixed:=arrays a _de (_ax.trans _axis) (by rw [_ax];exact _lanes)
  have _fit' : B.blockCharge*s w≤u w+1-w/2 := _fit.trans_eq _axis
  have limits:=iterator _fit' a β 0 cur _alph _placed _ptr
  rw [←_axis] at limits
  change a.TraceLimits (2^w) cur ops 0 (2^(3*w/5)) at limits
  have table:=limits.tables
  rw [Archive.directory_length] at table
  have heads : stop.header=a.cursor.header+64*ops.length := header_finish ..
  have header:=_placed.header
  have dense:=_placed.dense
  have seed:=_placed.seed
  have start:=_placed.records
  have floor:=_placed.heap
  have control:=_placed.control
  have amt:=limits.controls
  have room : a.cursor.heap≤cur.val := by omega
  have maxHeap : stop.heap≤a.control := by rw [show stop.heap=_ from heap_finish ..,←_ptr];exact amt
  have degree : 2*a.initialDegree≤directoryCap B := by rw [_de];unfold directoryCap;omega
  have count : a.seedLayer.count=(k+1)*2^(k+1) := by change a.axes*a.remainingLanes=_;rw [_ax,_lanes]
  have headCount:=node _fit'
  rw [←_axis] at headCount
  have large : 8*((k+1)*2^(k+1)+(ops.map Stage.heapWords).sum)≤traceUnit w := headCount.2.2.1
  have wt:=node_counts_heap ops
  obtain ⟨_,top,wordRoom⟩:=trace_sector (w:=w) (by omega)
  have inside : traceUnit w<2^(64*w) := by omega
  refine ⟨degree,by omega,?_,room,by omega,?_,by omega⟩
  · rw [Archive.metadataEnd];have:=fixed.2.2;omega
  · rw [_placed.node,count];omega

theorem eventual_recovery_geometry {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop,∀ {k : ℕ} (_axis : k+1=u w+1-w/2)
      (_fit : B.blockCharge*s w≤k+1)
      (a : Archive) (_placed : ArchivePlacement a (traceBase w) w)
      (_alph : a.K=B.alphabetCap) (_de : a.initialDegree=2^B.exponent 0)
      (_ax : a.axes=k+1) (_lanes : a.remainingLanes=2^(k+1)) (cur : Word (64*w))
      (_ptr : cur.val=a.control),
      let P:=B.repeat (s w)
      let rem:=k+1-P.charge
      let ops:=P.directory rem (k+1)
      let stop:=finish a.K ops a.cursor
      2*a.initialDegree≤directoryCap B ∧ stop.header≤a.initialRecords ∧
        a.metadataEnd≤a.cursor.heap ∧ a.cursor.heap≤cur.val ∧ stop.header≤a.cursor.heap ∧
        a.cursor.node+a.seedLayer.count+(ops.map Stage.nodes).sum+(ops.map successors).sum≤2^(64*w) ∧
        stop.heap≤a.control+64 := by
  filter_upwards [eventual_recovery_geometry_at B scale] with w room
  intro k _axis _fit a _placed
  exact room _axis _fit a (traceBase w) _placed

end Hierarchy.TraceAdmission

end OAI
