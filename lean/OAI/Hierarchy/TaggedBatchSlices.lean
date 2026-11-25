import OAI.Hierarchy.TaggedSlices
import OAI.Hierarchy.TaggedBatchSliceData

namespace OAI
/-! # Payload slicing across entire amplified batches -/

noncomputable section
namespace Hierarchy.Tagged.Slices
open scoped Classical BigOperators
open Catalyst CatalystSubstitution.SharedProduct CorrectionFrame

variable {F : Type*} [Field F] {k h w m : ℕ} (s : ℕ)
  (v : Fin m → ℕ) (total : ∑ i, v i = w)

include total in
/-- Combine already-amplified slice batches, counting each batch once for
the loss of gap, independently of its multiplicity. -/
theorem batch (positive : 0 < m) (X : ∀ i, Approximation F k (s*pins h (v i))) :
    ∃ Y : Approximation F k (s*pins h w), Y.size ≤ ∑ i, (X i).size ∧
      ∀ G : ℝ, (∀ i, (X i).Gap (dataProduct s (coeff F h (v i))) G) →
        Y.Gap (dataProduct s (coeff F h w)) (G-2*(k:ℝ)*(m:ℝ)) := by
  let : Nonempty (Fin m) := ⟨⟨0,positive⟩⟩
  obtain ⟨Y,size,prices⟩ := exists_product (fun i => s*pins h (v i)) (batchPin s v total) X
    (fun i => dataProduct s (coeff F h (v i)))
  refine ⟨Y,?_,fun G hg => ?_⟩
  · have shared := pins_le_sum (h:=h) v total positive
    have bound := Nat.mul_le_mul_left s shared
    rw [Finset.mul_sum] at bound
    omega
  · have eq := funext (batch_coeff (F:=F) s v total (h:=h))
    simpa only [eq,Fintype.card_fin] using prices G hg

end Hierarchy.Tagged.Slices

end
end OAI
