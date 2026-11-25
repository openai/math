import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeFactor

/-! # Coefficients of the prime-axis presentation at two

The prime-axis factorization is formed over the cyclotomic order before
extending scalars to either jet. Every divisor of its odd conductor
supplies separated Fourier nodes in the order itself.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial

variable {M m : ℕ}

private theorem cyclotomicCoefficients_nontrivial_aux (R : Type*) [CommRing R] [Nontrivial R]
    {k : ℕ} (hk : 0 < k) : Nontrivial (CyclotomicCoefficients R k) := by
  apply (AdjoinRoot.nontrivial_iff_of_monic (cyclotomic.monic k R)).mpr
  rw [degree_eq_natDegree (cyclotomic.monic k R).ne_zero, natDegree_cyclotomic]
  exact_mod_cast Nat.totient_pos.mpr hk

/-- The odd cyclotomic coefficient algebra is nontrivial. -/
theorem atTwoCoefficients_nontrivial (hM : 0 < M) :
    Nontrivial (CyclotomicCoefficients TwoLocalQuadratic M) := by
  let : Nontrivial TwoLocalQuadratic :=
    cyclotomicCoefficients_nontrivial_aux TwoLocalBase (by decide : 0 < 3)
  exact cyclotomicCoefficients_nontrivial_aux TwoLocalQuadratic hM

/-- A positive-length jet over the cyclotomic order remains nontrivial. -/
theorem atTwoJet_nontrivial {h : ℕ} (hM : 0 < M) (hh : 0 < h) :
    Nontrivial (IntegralJet M h) := by
  let : Nontrivial (CyclotomicCoefficients TwoLocalQuadratic M) :=
    atTwoCoefficients_nontrivial hM
  apply (AdjoinRoot.nontrivial_iff_of_monic (monic_X_pow h)).mpr
  rw [degree_X_pow]
  exact_mod_cast hh

/-- Odd integer scalars are invertible in the cyclotomic order at two. -/
theorem atTwoCoefficients_isUnit_odd (M : ℕ) {k : ℕ} (hk : Odd k) :
    IsUnit (k : CyclotomicCoefficients TwoLocalQuadratic M) := by
  have h : IsUnit (k : TwoLocalBase) := isUnit_natCast_protectedRationals hk.pos.ne' (by
    simpa using Nat.coprime_two_left.mpr hk)
  let f := (algebraMap TwoLocalQuadratic (CyclotomicCoefficients TwoLocalQuadratic M)).comp
    (algebraMap TwoLocalBase TwoLocalQuadratic)
  simpa using h.map f

/-- Before passage to the jets, every divisor of the conductor supplies
a unit root whose distinct Fourier powers differ by units. -/
theorem atTwoCoefficients_axisRoot (hM : Odd M) (hm : m ∣ M) :
    ∃ u : (CyclotomicCoefficients TwoLocalQuadratic M)ˣ,
      (u : CyclotomicCoefficients TwoLocalQuadratic M) =
        AdjoinRoot.root (cyclotomic M TwoLocalQuadratic)^(M/m) ∧
      u^m = 1 ∧ ∀ i j : Fin m, i ≠ j →
        IsUnit ((u : CyclotomicCoefficients TwoLocalQuadratic M)^i.val -
          (u : CyclotomicCoefficients TwoLocalQuadratic M)^j.val) := by
  have hξ := cyclotomicCoordinate_isRoot TwoLocalQuadratic M (RingHom.id _)
  obtain ⟨hpow, hsep⟩ := cyclotomicNodePowers hξ hM.pos (atTwoCoefficients_isUnit_odd M hM) hm
  obtain ⟨u, hu⟩ := IsUnit.of_pow_eq_one hpow (Nat.pos_of_dvd_of_pos hm hM.pos).ne'
  exact ⟨u, hu, Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_one, hu] using hpow),
    by simpa only [hu] using hsep⟩


/-- The nonscalar factorization on a selected prime axis, over the cyclotomic
order before either deformation endpoint. -/
theorem atTwoCoefficients_primeFactor {p : ℕ} [Fact p.Prime] (hM : Odd M)
    (hp : p % 4 = 3) (hp7 : 7 ≤ p) (hd : (p-1)/2 ∣ M) :
    let O := CyclotomicCoefficients TwoLocalQuadratic M
    letI : Nontrivial O := atTwoCoefficients_nontrivial hM.pos
    ∃ u : Oˣ, (u : O) = AdjoinRoot.root (cyclotomic M TwoLocalQuadratic)^(M/((p-1)/2)) ∧
      u^((p-1)/2) = 1 ∧
      (∀ i j : Fin ((p-1)/2), i ≠ j → IsUnit ((u:O)^i.val - (u:O)^j.val)) ∧
      Nonempty (AtTwoPrimeFactor O (PrimeAxisCosets.ofPrime p hp) u hp7) := by
  let : Nontrivial (CyclotomicCoefficients TwoLocalQuadratic M) := atTwoCoefficients_nontrivial hM.pos
  obtain ⟨u,hu₀,hu,hs⟩ := atTwoCoefficients_axisRoot hM hd
  obtain ⟨hpo,hmo⟩ := primeAxis_odd_parameters hp
  exact ⟨u, hu₀, hu, hs, ⟨atTwoPrimeFactor _ _ u hp hp7 (atTwoCoefficients_isUnit_odd M hpo)
    (atTwoCoefficients_isUnit_odd M hmo) hu hs⟩⟩

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
