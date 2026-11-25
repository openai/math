import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-! # Reduced residue fibers of a cyclotomic algebra -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- When the order is a unit, the cyclotomic algebra has reduced fibers over all
maximal ideals of the coefficient ring. -/
theorem primeAxisFiber_isReduced {O : Type*} [CommRing O] (p : ℕ)
    (hp : IsUnit (p : O)) (m : Ideal O) [m.IsMaximal] :
    IsReduced (AdjoinRoot (Polynomial.cyclotomic p O) ⧸
      m.map (AdjoinRoot.of (Polynomial.cyclotomic p O))) := by
  let := Ideal.Quotient.field m
  have hu : IsUnit (p : O ⧸ m) := by simpa using hp.map (Ideal.Quotient.mk m)
  have : NeZero (p : O ⧸ m) := ⟨hu.ne_zero⟩
  let e := AdjoinRoot.quotEquivQuotMap (Polynomial.cyclotomic p O) m
  have : IsReduced (Polynomial (O ⧸ m) ⧸ Ideal.span
      {(Polynomial.cyclotomic p O).map (Ideal.Quotient.mk m)}) := by
    rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton,
      Polynomial.map_cyclotomic]
    exact (Polynomial.separable_cyclotomic p (O ⧸ m)).squarefree.isRadical
  exact isReduced_of_injective e e.injective

end FiniteFourier
end LinearAlgebra
end OAI
