import OAI.Computability.BorderVNP.DiagonalTallyAllocatedCellSource
import OAI.Computability.BorderVNP.RoutingISATypedTaskAllocation
import OAI.Computability.BorderVNP.CellTeamPreparedPaths

/-! # Actual report operands survive the typed cell program and selected cube lookups -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalTallyAllocation DiagonalTallyRAM DiagonalTallyMaterialize
open private supplied_unchanged from OAI.Computability.BorderVNP.DiagonalTallyRAMAllocatedRun

variable {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}

/-- The actual task-builder, four-word patch prepass, packet initializer and signed private
cell calls preserve the whole indirect input stream. The arithmetic checks use the physical
public descriptor tail, the merged-count allocation and the true per-cell task arena strides. -/
theorem ReportAllocation.supplied_after_calls {w : ℕ} {Site : Type}
    (h : ReportAllocation pre post banks l cs q) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (m m₁ : Memory w) (task : TypedTaskBuilder.Layout) (owned : ℕ → CellPacket.Supplement.Batch.Owned Site)
    (zeroLo : banks.bankStart+banks.cells*banks.stride ≤ l.zeroAddr) (zeroHi : l.zeroAddr<pre.start)
    (old : DiagonalTallyMaterialize.supplied m (cellEnd cs q) q.descriptors (cellOperands cs q))
    (published : readings m₁=task.published (readings m))
    (ar : task.Arenas (readings m) w fun i => (owned i).typed)
    (calls : pre.merged ≤ task.calls) (table : pre.merged ≤ task.tasks)
    (end_ : task.bursts+task.burstStride*task.cells ≤ post.start)
    (taskFrame : task.frame=l.frame)
    (supp : ∀ i < task.before (readings m) task.cells,
      pre.merged ≤ (owned i).layout.merged ∧ (owned i).layout.merged<post.start ∧ (owned i).layout.tail+12 ≤ banks.bankStart) :
    let count := task.before (readings m) task.cells
    let patched := CellPacket.Supplement.Batch.written m₁ (fun i => (owned i).cell) count
    let mt := TypedBatch.written patched (fun i => (owned i).typed) count
    (pub 0).val+15<2^w → (CellDispatch.Frame.ofMemory pub mt).base+3*(CellDispatch.Frame.ofMemory pub mt).count ≤ 2^w →
    ∀ {s es t mf}, Runs pub mac callOwnedCells s mt es t mf →
      DiagonalTallyMaterialize.supplied mf (cellEnd cs q) q.descriptors (cellOperands cs q) := by
  intro count patched mt fp room s es t mf run
  apply supplied_unchanged _ _ _ _ _ old
  intro a read
  obtain ⟨lo,middle,_⟩ := h.read_extent zeroLo zeroHi read
  have fpast := h.frameBefore
  have beforePacked : post.start ≤ post.packed := by
    simp only [AfterTasks.packed,AfterTasks.ids,AfterTasks.lookupRefs,AfterTasks.lookupRows]; omega
  have rc := ar.calls
  have rt := ar.table
  have rs := ar.scratch
  have clear : ¬task.outputAt a := by
    rintro (tasks|⟨c,hc,e⟩|e)
    · omega
    · change a=task.calls+3*c at e
      omega
    · rw [taskFrame] at e
      omega
  apply CellPacket.Supplement.Batch.preserved_after_calls task m m₁ owned published a clear _ fp room run
  intro i hi
  obtain ⟨mergedLo,mergedHi,tail⟩ := supp i hi
  have v := (TypedTaskBuilder.global_spec task (readings m) hi).1
  obtain ⟨c,sr,br⟩ := ar.starts i hi
  obtain ⟨ps,bs⟩ := ar.widths i hi
  have scratch := Nat.mul_le_mul_left task.scratchStride v
  have burst := Nat.mul_le_mul_left task.burstStride v
  rw [Nat.mul_succ] at scratch burst
  refine ⟨⟨by change a≠(owned i).layout.merged; omega,.inr (tail.trans lo)⟩,?_⟩
  simp only [TypedBatch.Task.Outside,sr,br,c,TypedTaskBuilder.Layout.call]
  omega

/-- The actual two-window preservation returned by the native selected-ID lookup keeps
all cell operands in place, even though they lie on both sides of its write region. -/
theorem ReportAllocation.supplied_after_lookup {w : ℕ}
    (h : ReportAllocation pre post banks l cs q) (m mt : Memory w) (count : ℕ)
    (zeroLo : banks.bankStart+banks.cells*banks.stride ≤ l.zeroAddr) (zeroHi : l.zeroAddr<pre.start)
    (old : DiagonalTallyMaterialize.supplied m (cellEnd cs q) q.descriptors (cellOperands cs q))
    (vertices : count ≤ post.bound.vertices)
    (preserved : ∀ a, a<post.lookupRows ∨ post.ids+count ≤ a → mt a=m a) :
    DiagonalTallyMaterialize.supplied mt (cellEnd cs q) q.descriptors (cellOperands cs q) := by
  apply supplied_unchanged _ _ _ _ _ old
  intro a read
  obtain ⟨_,middle,_⟩ := h.read_extent zeroLo zeroHi read
  have limit : pre.merged ≤ pre.limit := by
    simp only [BeforeTasks.limit,BeforeTasks.bundleTable,BeforeTasks.ranges,BeforeTasks.six,BeforeTasks.four]; omega
  have gap := h.preBefore
  have ids := (post.lookup_separated vertices).2.2.1
  apply preserved
  change a<post.start ∨ post.ids+count ≤ a
  omega

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
