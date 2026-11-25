import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleSystem
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleFreeCounts
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Specialization of the prime routing system

All label directions, rectangle sets, and weights may be fixed over ℤ[1/ℓ]
before choosing the arithmetic field. Base change acts on scalar weights.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open scoped Classical

namespace PrimeRectangleSystem

/-- Apply a coefficient homomorphism to the two families of rectangle weights. -/
def map {K E : Type*} [CommRing K] [CommRing E] {ℓ L b : ℕ}
    (S : PrimeRectangleSystem K ℓ L b) (f : K →+* E) : PrimeRectangleSystem E ℓ L b where
  D := S.D
  dimension_le := S.dimension_le
  a := S.a
  d := S.d
  diagonal_ne_zero := S.diagonal_ne_zero
  gram := S.gram
  chargedWeight := fun R => f (S.chargedWeight R)
  freeWeight := fun R => f (S.freeWeight R)
  identity v w := by
    simpa only [map_add, map_sum, apply_ite f, map_zero, map_one] using
      congrArg f (S.identity v w)

/-- A single choice of rectangle data over ℤ[1/ℓ]. -/
def integral (ℓ L b : ℕ) [Fact ℓ.Prime] : PrimeRectangleSystem (Localization.Away (ℓ : ℤ)) ℓ L b :=
  (exists_primeRectangleSystem _ ℓ L b (by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (ℓ : ℤ)) (ℓ : ℤ))).some

/-- Specialization of the same integral routing to every ring with invertible ℓ. -/
def specialize (K : Type*) [CommRing K] (ℓ L b : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) :
    PrimeRectangleSystem K ℓ L b :=
  (integral ℓ L b).map (Localization.awayLift (Int.castRingHom K) (ℓ : ℤ) (by simpa using hℓ))

end PrimeRectangleSystem
end

end

end FiniteFourier
end LinearAlgebra
end OAI
