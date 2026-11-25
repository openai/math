import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedCancellation
import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedConstant
import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedPieces

/-! # Combining the constant, charged, and free parts of a pencil -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open scoped Classical

variable {K : Type*} [CommSemiring K]
variable {L W X A J C U : Type} [Fintype A] [Fintype J] [Fintype C] [Fintype U]

/-- Every copy receives its own query pencil on its own inputs. -/
theorem routedPencil_assembly
    (cs ct : C → Set L) (fs ft : U → Set L) (cw : C → K) (fw : U → K)
    (hid : ∀ v w : L,
      (∑ r, if v ∈ cs r ∧ w ∈ ct r then cw r else 0) +
      (∑ r, if v ∈ fs r ∧ w ∈ ft r then fw r else 0) = if v = w then 1 else 0)
    (B₀ : Matrix W W K) (B : A → J → Matrix W W K)
    (H : A → J → L → L → Matrix X X K) (Q : A → J → Matrix X X K)
    (hdiag : ∀ a j v, H a j v v = Q a j) :
    routedConstantMatrix B₀ + (∑ a, (
      (∑ r : C, ∑ j, routedRectangleMatrix (cs r) (ct r) (cw r) (routedPencilTerm (B a j) (H a j))) +
      (∑ r : U, routedRectangleMatrix (fs r) (ft r) (fw r) (∑ j, routedPencilTerm (B a j) (H a j))))) =
      routedPencilMatrix B₀ B Q := by
  simp_rw [routedPencil_cancellation cs ct fs ft cw fw hid]
  ext ⟨⟨w,t⟩,y⟩ ⟨⟨v,u⟩,x⟩
  by_cases h : v = w
  · subst w
    simp [routedConstantMatrix, routedLabelDiagonal, routedPencilMatrix, Matrix.sum_apply,
      routedPencilTerm, hdiag]
  · simp [routedConstantMatrix, routedLabelDiagonal, routedPencilMatrix, Matrix.sum_apply, h, Ne.symm h]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
