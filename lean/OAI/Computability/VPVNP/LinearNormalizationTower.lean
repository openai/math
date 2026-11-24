import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Descending integrality along a change of generators

If the old generators are integral over a new subalgebra, all their
polynomial expressions belong to its integral closure. Any element integral
over the old generators is consequently integral over the new subalgebra.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LinearNormalization

variable {K A I : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem integral_over_new_generators (B : Subalgebra K A) (g : I → A)
    (hgen : ∀ i, IsIntegral B (g i)) (a : A)
    (ha : IsIntegral (Algebra.adjoin K (Set.range g)) a) : IsIntegral B a := by
  let T := integralClosure B A
  have hle : Algebra.adjoin K (Set.range g) ≤ T.restrictScalars K :=
    Algebra.adjoin_le (by rintro x ⟨i, rfl⟩; exact hgen i)
  let f := Subalgebra.inclusion hle
  have h : IsIntegral T a :=
    RingHom.IsIntegralElem.of_comp (f := f.toRingHom) (g := algebraMap T A) ha
  exact isIntegral_trans (A := T) a h

end LinearNormalization

end VPVNP
end Computability
end OAI
