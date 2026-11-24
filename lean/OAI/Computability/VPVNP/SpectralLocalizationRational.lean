import Mathlib.RingTheory.Localization.FractionRing

/-!
# Rational scalars in the localization of a spectral semiring

In characteristic zero the images of the positive natural numbers become
units when we invert the nonzero elements of the semiring. This supplies the
rational scalar action used in the algebraic separation argument. Clearing
denominators then writes each nonnegative rational as a ratio of naturals.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

/-- A commutative ring in which positive natural numbers are units is a
rational algebra by the universal property of the localization of `ℤ`. -/
@[instance_reducible]
noncomputable def ratAlgebraOfUnits (A : Type*) [CommRing A]
    (hunit : ∀ n : ℕ, n ≠ 0 → IsUnit (n : A)) : Algebra ℚ A := by
  refine (IsLocalization.lift (S := ℚ) (M := Submonoid.pos ℤ)
    (g := Int.castRingHom A) ?_).toAlgebra
  intro x
  have hx : 0 < x.val := x.property
  have hnat := hunit x.val.toNat (by omega)
  change IsUnit (x.val : A)
  rwa [← Int.cast_natCast, Int.toNat_of_nonneg hx.le] at hnat

/-- Clearing the positive denominator of a nonnegative rational in any
rational algebra gives its natural numerator. -/
theorem den_mul_algebraMap_eq_num_toNat (A : Type*) [CommRing A] [Algebra ℚ A]
    (q : ℚ) (hq : 0 ≤ q) :
    (q.den : A) * algebraMap ℚ A q = (q.num.toNat : A) := by
  have h := congrArg (algebraMap ℚ A) (Rat.den_mul_eq_num q)
  simp only [map_mul, map_natCast, map_intCast] at h
  rw [← Int.cast_natCast q.num.toNat, Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)]
  exact h

end Spectral

end VPVNP
end Computability
end OAI
