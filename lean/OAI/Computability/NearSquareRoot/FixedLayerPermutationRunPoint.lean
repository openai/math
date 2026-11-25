import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepDispatch
import OAI.Computability.NearSquareRoot.SynchronizedPermutationUniversal

/-! # A live Fourier batch as an input to the universal native switch program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer.PermutationBatch
open IntegerMultiplication Code FixedCandidate FixedPoint Space DigitPacking
open SynchronizedPermutationBudget SynchronizedLayers.ScheduleProgram
open Benes.PackedBatchHeader (PassPoint)

noncomputable section

private theorem batch_bounds {D B : ℕ} {a : (Bool × ℕ) × ℕ} (valid : a ∈ Benes.batchOrder D B) :
    a.1.2 < D ∧ a.2 < B := by
  obtain ⟨stage,inside,member⟩ := List.mem_flatMap.mp valid
  obtain ⟨batch,hbatch,rfl⟩ := List.mem_map.mp member
  refine ⟨?_,List.mem_range.mp hbatch⟩
  rcases List.mem_append.mp inside with left | right
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp left
    exact List.mem_range.mp hj
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp right
    exact List.mem_range.mp (List.mem_reverse.mp hj)

variable {I : Type} {n : I → ℕ} {h : ∀ i, FixedCandidate.Directory (n i)} {dir : I → Bool}
  (z : PermutationBatch n h dir) (hd : ∀ i, 4 ≤ (box (n i)).length)
  {D : ℕ} (big : ∀ i, BoxPasses (addressBits (n i)) D 2)

/-- Read the actual row, switch depth and batch number of the generated Fourier
ticket. The membership proof supplies the native interpreter's range checks. -/
def point : PassPoint where
  k := addressBits (n z.1.val.instanceIndex)
  D := D
  dir := dir z.1.val.instanceIndex
  row := z.1.val.position
  kind := z.1.tag
  budget := big z.1.val.instanceIndex
  long := hd z.1.val.instanceIndex
  side := z.2.1.val.1.1
  depth := ⟨z.2.1.val.1.2,(batch_bounds z.2.1.property).1⟩
  batch := ⟨z.2.1.val.2,(batch_bounds z.2.1.property).2⟩

/-- Both descriptions emit the identical registry of row banks and controls. -/
theorem point_descriptor : (point z hd big).descriptor = descriptor z D := rfl

/-- Native binary address words read the current Fourier record in the tape's
numeric order after any permutation from previous batches. -/
theorem point_recordAddress :
    let x := point z hd big
    letI := BoxFin.modulus_neZero x.budget.valid
    Benes.PackedBatchHeader.recordAddress x.budget.valid x.long =
      (Controlled.flatAddress 2 x.k).trans (rank z hd) := by rfl

/-- The batched native control switches use the very tables and ticket indices
selected by the row dispatcher, including its forward or adjoint direction. -/
theorem point_switch :
    let x := point z hd big
    Benes.batchStage (fun b : Fin ((CoprimeBox.box x.k).length/4) => b.val / SynchronizedPermutationBudget.capacity x.k)
      (BoxFin.physicalWidth (box := CoprimeBox.box x.k))
      (fun _ : Unit => ShortFourier.BatchWord.PermDirectory.switchTable x.dir x.row.val)
      (x.side,x.depth.val) x.batch.val = switch z := by rfl

end
end FixedLayer.PermutationBatch

end NearSquareRoot
end Computability
end OAI
