import OAI.LinearAlgebra.FiniteFourier.ProtectedCyclotomicDomain

/-! # Fourier roots over protected rationals

The monic cyclotomic quotient contains its tautological primitive root.
Every integer coprime to the protected primes is a unit in the coefficient
extension, including the orders of the Fourier kernels used in the shear.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

/-- The explicit coefficient extension for a protected Fourier kernel. -/
abbrev ProtectedCyclotomic (L : Finset ℕ) (n : ℕ) :=
  AdjoinRoot (cyclotomic n (protectedRationals L))

/-- The tautological root of the cyclotomic quotient has exact order `n`. -/
theorem protectedCyclotomic_primitive (L : Finset ℕ) (n : ℕ) (hn : 0 < n) :
    IsPrimitiveRoot (AdjoinRoot.root (cyclotomic n (protectedRationals L))) n := by
  let := protectedCyclotomic_isDomain L n hn
  let : CharZero (ProtectedCyclotomic L n) := charZero_of_injective_ringHom
    (AdjoinRoot.of.injective_of_monic_of_degree_pos (cyclotomic.monic _ _)
      (degree_cyclotomic_pos n _ hn))
  apply (isRoot_cyclotomic_iff_charZero hn).mp
  simpa only [map_cyclotomic] using AdjoinRoot.isRoot_root (cyclotomic n (protectedRationals L))

/-- All admissible integer orders stay invertible after adjoining a root. -/
theorem protectedCyclotomic_isUnit {L : Finset ℕ} (n : ℕ) {d : ℕ} (hd : d ≠ 0)
    (hc : ∀ p ∈ L, p.Coprime d) : IsUnit (d : ProtectedCyclotomic L n) := by
  simpa using (isUnit_natCast_protectedRationals hd hc).map
    (algebraMap (protectedRationals L) (ProtectedCyclotomic L n))

end FiniteFourier
end LinearAlgebra
end OAI
