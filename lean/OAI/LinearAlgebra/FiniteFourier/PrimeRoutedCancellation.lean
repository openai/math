import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedPadding

/-! # Cancellation of off-label transfers in the routed pencil

For fixed source and destination, all incident rectangles carry the same
cross-label operator. Their weights therefore multiply that operator by
the corresponding entry of the identity. Summation over the queries can
take place inside a free rectangle.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open scoped Classical

variable {K : Type*} [CommSemiring K] {L W X C U J : Type}

abbrev RoutedRegister (L W X : Type) := ((L × W) × X)

/-- Keep the diagonal label blocks of a transfer on the full row bank. -/
def routedLabelDiagonal (M : Matrix (RoutedRegister L W X) (RoutedRegister L W X) K) :
    Matrix (RoutedRegister L W X) (RoutedRegister L W X) K :=
  fun o i => if i.1.1 = o.1.1 then M o i else 0

/-- A weighted resolution of the identity cancels off-label transfers, even
when the block for each ordered pair of labels is different. The uncharged
rectangles sum over the complete pencil at once. -/
theorem routedPencil_cancellation [Fintype C] [Fintype U] [Fintype J]
    (cs ct : C → Set L) (fs ft : U → Set L) (cw : C → K) (fw : U → K)
    (hid : ∀ v w : L,
      (∑ r, if v ∈ cs r ∧ w ∈ ct r then cw r else 0) +
      (∑ r, if v ∈ fs r ∧ w ∈ ft r then fw r else 0) = if v = w then 1 else 0)
    (M : J → Matrix (RoutedRegister L W X) (RoutedRegister L W X) K) :
    (∑ r : C, ∑ j : J, routedRectangleMatrix (cs r) (ct r) (cw r) (M j)) +
      (∑ r : U, routedRectangleMatrix (fs r) (ft r) (fw r) (∑ j, M j)) =
    routedLabelDiagonal (∑ j, M j) := by
  ext o i
  let g := ∑ j, M j o i
  have charged (r : C) :
      (∑ j, routedRectangleMatrix (cs r) (ct r) (cw r) (M j) o i) =
        (if i.1.1 ∈ cs r ∧ o.1.1 ∈ ct r then cw r else 0) * g := by
    by_cases h : i.1.1 ∈ cs r ∧ o.1.1 ∈ ct r <;>
      simp [routedRectangleMatrix, h, g, Finset.mul_sum]
  have free (r : U) :
      routedRectangleMatrix (fs r) (ft r) (fw r) (∑ j, M j) o i =
        (if i.1.1 ∈ fs r ∧ o.1.1 ∈ ft r then fw r else 0) * g := by
    by_cases h : i.1.1 ∈ fs r ∧ o.1.1 ∈ ft r <;>
      simp [routedRectangleMatrix, h, g, Matrix.sum_apply]
  simp only [Matrix.add_apply, Matrix.sum_apply, charged, free, ← Finset.sum_mul, ← add_mul, hid]
  by_cases h : i.1.1 = o.1.1 <;> simp [routedLabelDiagonal, h, g, Matrix.sum_apply]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
