import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicPrimePresentation
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeCRT

/-! # The scalar and binomial coordinate change on a dyadic-list prime axis

The singleton coordinate receives the sum of all inputs. The nonscalar coordinates
are the Fourier transform on the multiplicative group, scaled by units and corrected
in the constant coefficient by the input at the zero address.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
namespace Deformation

open Polynomial Module
open scoped BigOperators

variable {R : Type*} [CommRing R] [Nontrivial R] {p : ℕ} [Fact p.Prime] (C : PrimeAxisOrbit p)
local notation "m" => (p - 1)
local notation "Aₚ" => AdjoinRoot (cyclotomic p R)

/-- A Rader Fourier transform on precisely the nonzero addresses. -/
def dyadicPrimeSums (u : Rˣ) (v : Fin m → R) (j : Fin m) : R :=
  ∑ t : Fin m, (u:R)^(j.val * t.val) * v t

omit [Nontrivial R] in
private theorem dyadicPrime_transform_orbit (u : Rˣ) (hm : IsUnit ((m : ℕ) : R))
    (hu : u^m = 1) (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val))
    (v : Fin m → R) :
    ∑ t : Fin m, v t • primeAxisCharacter R p (C.equiv t) =
      ∑ j : Fin m, ((↑hm.unit⁻¹ : R) * dyadicPrimeSums u v j) • dyadicPrimeFourier R C u j := by
  simp_rw [dyadicPrimeOrbit_fourierExpansion R C u hm hu hs, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_smul, dyadicPrimeSums, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- The forward coordinate change, including the singleton axis, with the units used
by the inverse. It is an algebra isomorphism, so pointwise multiplication in the
two factors recovers cyclic multiplication. -/
theorem exists_dyadicPrimeCoordinates (u : Rˣ) (hodd : 1 < m) (hpR : IsUnit (p:R))
    (hm : IsUnit ((m : ℕ) : R)) (hu : u^m = 1)
    (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val)) :
    ∃ (β : Rˣ) (d : Fin m → Rˣ)
        (e : BinomialAxis p (1 : R) ≃ₐ[R] R × BinomialAxis m (β:R)),
      (↑(d ⟨0,by omega⟩) : R) = -1 ∧
      ∀ (a : R) (v : Fin m → R),
        e (algebraMap R _ a + ∑ t : Fin m, v t • primeCyclicBasis R p (C.equiv t)) =
          (a + ∑ t, v t, algebraMap R _ a + ∑ j : Fin m,
            (((↑hm.unit⁻¹ : R) * dyadicPrimeSums u v j) * (d j : R)) •
              binomialBasis (by omega) (β:R) j) := by
  classical
  let z : Fin m := ⟨0, by omega⟩
  obtain ⟨β,Y,scales,b,_,hY,hbasis,hscale⟩ := exists_dyadicPrimeBinomialBasis C u hodd hpR hm hu hs
  let F := binomialPresentation (by omega) (β:R) (Y:Aₚ) hY b hbasis
  have hFw (j : Fin m) : F (binomialBasis (by omega) (β:R) j) = b j := by
    rw [binomialBasis_apply, map_pow, binomialPresentation_root, hbasis]
  have hFF (j : Fin m) : F.symm (dyadicPrimeFourier R C u j) =
      (↑(scales j)⁻¹ : R) • binomialBasis (by omega) (β:R) j := by
    apply F.injective
    rw [F.apply_symm_apply, map_smul, hFw, hscale, smul_smul, Units.inv_mul, one_smul]
  let E := (primeCyclicCRT R p hpR).trans ((AlgEquiv.refl : R ≃ₐ[R] R).prodCongr F.symm)
  refine ⟨β, fun j => (scales j)⁻¹, E, ?_, ?_⟩
  · have hbz := hscale z
    have hb₀ : b z = 1 := by simp [hbasis, z]
    have hγz : dyadicPrimeFourier R C u z = - b z := by
      rw [hb₀]
      exact dyadicPrimeFourier_zero R C u _
    rw [hγz] at hbz
    have hcast : (scales z : R) = -1 := by
      have h := congrArg (fun x => b.repr x z) hbz
      simp only [map_smul, map_neg, Basis.repr_self, Finsupp.single_eq_same,
        Finsupp.smul_apply, Finsupp.neg_apply, smul_eq_mul, mul_neg, mul_one] at h
      linear_combination h
    have hUnits : scales z = -1 := Units.ext (by simpa using hcast)
    change (↑(scales z)⁻¹ : R) = -1
    rw [hUnits]
    simp
  · intro a v
    have hcrt (t : Fin m) := primeCyclicCRT_basis R p hpR (C.equiv t : ZMod p)
    change (AlgEquiv.refl.prodCongr F.symm) (primeCyclicCRT R p hpR _) = _
    rw [map_add, map_sum, AlgEquiv.commutes]
    simp only [map_smul, hcrt]
    apply Prod.ext
    · simp [Algebra.smul_def, Prod.fst_sum]
    · change F.symm (((algebraMap R (R × Aₚ)) a + ∑ t, v t • (1, primeAxisCharacter R p (C.equiv t))).2) = _
      simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd]
      rw [dyadicPrime_transform_orbit C u hm hu hs, map_add, map_sum]
      change F.symm (algebraMap R Aₚ a) + _ = _
      rw [AlgEquiv.commutes]
      simp only [map_smul, hFF, smul_smul]

end Deformation

end

end FiniteFourier
end LinearAlgebra
end OAI
