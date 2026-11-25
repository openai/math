import OAI.LinearAlgebra.FiniteFourier.ProtectedRationals

/-! # Cyclotomic domains over the protected rationals

Divisibility by a monic polynomial descends through an injective coefficient
map. Hence the rational cyclotomic polynomial stays prime after restricting
coefficients to any protected subring of the rationals.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

/-- The cyclotomic quotient of the protected rationals is a domain for every
positive order, independently of the protected primes. -/
theorem protectedCyclotomic_isDomain (L : Finset ℕ) (n : ℕ) (hn : 0 < n) :
    IsDomain (AdjoinRoot (cyclotomic n (protectedRationals L))) := by
  let φ := (protectedRationals L).subtype
  let P := cyclotomic n (protectedRationals L)
  have hP : P.Monic := cyclotomic.monic _ _
  have hQ : Prime (P.map φ) := by
    simpa [P] using (cyclotomic.irreducible_rat hn).prime
  apply AdjoinRoot.isDomain_of_prime
  refine ⟨hP.ne_zero, fun hu => hQ.not_isUnit (hu.map (Polynomial.mapRingHom φ)), ?_⟩
  intro a b hab
  have hab' := Polynomial.map_dvd φ hab
  rw [Polynomial.map_mul] at hab'
  exact (hQ.dvd_or_dvd hab').imp (map_dvd_map φ Subtype.val_injective hP).mp
    (map_dvd_map φ Subtype.val_injective hP).mp

end FiniteFourier
end LinearAlgebra
end OAI
