import OAI.Computability.NearSquareRoot.SynchronizedBoxPhysicalLayout
import OAI.Computability.NearSquareRoot.SynchronizedRowMembership
import OAI.Computability.NearSquareRoot.PrecisionActualPhasePass

/-! # The actual scanned phase row equals the scheduled Fourier layer -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open Matrix IntegerMultiplication.Code SynchronizedBlocks SynchronizedPadding SynchronizedLayers
open SynchronizedLayers.ScheduleProgram BoxFin PhaseTable FixedPoint
open scoped Matrix

noncomputable section

variable {k : ℕ} [∀ i, NeZero (BoxFin.modulus (CoprimeBox.box k) i)]
    (h : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k))

private theorem phase_rowTensor {dir : Bool} (r : Bool × Row SlotDescriptor)
    (hr : r ∈ directedPlan (dir,tally k)) (hk : r.2.1 = kindCode .diagonal) (precision : ℕ) :
    rowMatrix (fun j z => (boxSlot (physicalLayout h) j z).matrix ((physicalLayout h).bits j)) r.2 =
      Matrix.diagonal (fun y => ∏ j, (readBlock r.2 j.val).elim 1 (fun z => actualBlockPhase h j precision z (y j))) := by
  let C (j : Fin ((CoprimeBox.box k).length/4)) (x : BlockAddress (BoxAxis (CoprimeBox.box k)) j) :=
    (readBlock r.2 j.val).elim 1 (fun z => actualBlockPhase h j precision z x)
  have eqn (j : Fin ((CoprimeBox.box k).length/4)) :
      ((readBlock r.2 j.val).map (fun z => (boxSlot (physicalLayout h) j z).matrix ((physicalLayout h).bits j))).getD 1 =
        diagonal (C j) := by
    cases hz : readBlock r.2 j.val with
    | none => simp [C,hz]
    | some z =>
      obtain ⟨hz',hk'⟩ := directed_read_spec hr j hz
      simp only [C,hz,Option.map_some,Option.getD_some,Option.elim_some]
      exact decode_phaseAt _ _ _ _ _ _ _ _ precision z hz' (kindCode_injective (hk'.trans hk))
  unfold rowMatrix
  rw [funext eqn, tensorMatrix_diagonal]

private theorem directed_diagonal {A S : Type} [Fintype S] [DecidableEq A]
    (flag : Bool) (f : S → A → ℂ) :
    (if flag then (diagonal (fun x => ∏ j, f j x))ᴴ else diagonal (fun x => ∏ j, f j x)) =
      diagonal (fun x => ∏ j, adjointValue flag (f j x)) := by
  cases flag <;> simp [adjointValue, diagonal_conjTranspose]

/-- Undo grouping: the directed layer is diagonal, with exactly one present
or idle phase coefficient per block and the direction chosen by the tape. -/
theorem boxRow_phase {dir : Bool} (hd : 4 ≤ (CoprimeBox.box k).length) (r : Bool × Row SlotDescriptor)
    (hr : r ∈ directedPlan (dir,tally k)) (hk : r.2.1 = kindCode .diagonal) (precision : ℕ) :
    boxRow (physicalLayout h) hd r =
      diagonal (fun x => ∏ j, adjointValue r.1
        ((readBlock r.2 j.val).elim 1 (fun z => actualBlockPhase h j precision z (regroup hd _ x j)))) := by
  rw [boxRow, phase_rowTensor h r hr hk precision, directed_diagonal, submatrix_diagonal_equiv]
  rfl

/-- On the flat physical address array the generated diagonal program applies
exactly the coefficients of this indexed row, including all idle blocks. -/
theorem flat_phaseRow {dir : Bool} (hd : 4 ≤ (CoprimeBox.box k).length)
    (t : Fin (directedPlan (dir,tally k)).length)
    (tag : (directedPlan (dir,tally k))[t.val].2.1 = kindCode .diagonal) :
    (boxRow (physicalLayout h) hd (directedPlan (dir,tally k))[t.val]).submatrix
      (recordIndex h).symm (recordIndex h).symm =
        diagonal (blockCoefficient h hd (scheduledBlockPhase h dir t.val)) := by
  have hr := List.getElem_mem (l := directedPlan (dir,tally k)) t.isLt
  rw [boxRow_phase h hd _ hr tag (70*guardedK k+3), submatrix_diagonal_equiv]
  apply congrArg diagonal
  funext x
  simp [blockCoefficient, scheduledBlockPhase, directedQuery]

omit [∀ i, NeZero (BoxFin.modulus (CoprimeBox.box k) i)] in
/-- Unit norm at every physical position follows from the generated coefficient tables. -/
theorem flat_phaseRow_unit (hd : 4 ≤ (CoprimeBox.box k).length) (dir : Bool) (t : ℕ) (j : Fin (2^k)) :
    ‖blockCoefficient h hd (scheduledBlockPhase h dir t) j‖ = 1 := by
  simp [blockCoefficient, norm_prod, scheduledBlockPhase_unit]

/-- The exact Euclidean isometry for this slot is the one used by the finite
precision primitive on the packed records. -/
theorem flat_phaseRow_apply {dir : Bool} (hd : 4 ≤ (CoprimeBox.box k).length)
    (t : Fin (directedPlan (dir,tally k)).length)
    (tag : (directedPlan (dir,tally k))[t.val].2.1 = kindCode .diagonal)
    (hu : ∀ j, ‖blockCoefficient h hd (scheduledBlockPhase h dir t.val) j‖ = 1)
    (x : EuclideanSpace ℂ (Fin (2^k))) :
    (boxRow (physicalLayout h) hd (directedPlan (dir,tally k))[t.val]).submatrix
      (recordIndex h).symm (recordIndex h).symm *ᵥ (fun j => x j) =
        (fun j => phaseLayerIsometry _ hu x j) := by
  rw [flat_phaseRow h hd t tag]
  funext j
  exact Matrix.mulVec_diagonal ..

end
end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
