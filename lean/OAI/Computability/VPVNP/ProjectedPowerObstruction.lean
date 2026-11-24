import OAI.Computability.VPVNP.BalancedPowerObstruction
import OAI.Computability.VPVNP.TensorPowerLengths

/-!
# Applying the balanced-cut obstruction to projected powers

A literal projection of each tensor power from the universal polynomial transfers
a circuit at an isolated small-circuit length to the largest power fitting there.
The exponent in the projection length bound multiplies the assumed circuit exponent.
A strict spectral cost gap then rules out arbitrarily large small-circuit lengths.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial WireTensor

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]

omit [Fintype J] in
@[simp] theorem partyExponent_univ_apply [DecidableEq J] (x : I → J) (i : I) (j : J) :
    partyExponent Finset.univ x (i, j) = if x i = j then 1 else 0 := by
  rw [partyExponent, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simp [Finsupp.single_apply]
  · intro i' _ hi
    simp [hi]
  · simp

omit [Fintype J] in
theorem partyExponent_univ_injective :
    Function.Injective (partyExponent (Finset.univ : Finset I) (J := J)) := by
  classical
  intro x y h
  funext i
  have hxy := DFunLike.congr_fun h (i, y i)
  simpa using hxy

/-- The selected coefficient of the set-multilinear tensor form is its array entry. -/
theorem coeff_partyForm {R : Type*} [CommSemiring R] (A : (I → J) → R) (a : I → J) :
    (∑ x : I → J, (∏ i, X (i, x i)) * C (A x) : MvPolynomial (I × J) R).coeff
      (partyExponent Finset.univ a) = A a := by
  classical
  have e : (∑ x : I → J, (∏ i, X (i, x i)) * C (A x) : MvPolynomial (I × J) R) =
      ∑ x, monomial (partyExponent Finset.univ x) (A x) := by
    simp only [partyExponent, monomial_sum_index, X]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  simp [e, coeff_monomial, partyExponent_univ_injective.eq_iff]

variable {k P : Type*} [Field k] [Fintype P]

/-- Under a strict spectral layout gap, a family of projected powers as in Section
4.2 precludes arbitrarily large small-circuit lengths for the original family. -/
theorem not_small_universal_of_power_projections
    (F : SpectralPoint k P) (place : I → P) (centers : Finset I → Bool → P) (A : (I → J) → k)
    (forms : (h : ℕ) → MvPolynomial (I × (Fin h → J)) k) (M D C : ℕ)
    (hM : 0 < M) (hD : 0 < D) (hC : 0 < C) (hI : 3 ≤ Fintype.card I) (hJ : 1 < Fintype.card J)
    (coeffs : ∀ h a, (forms h).coeff (partyExponent Finset.univ a) =
      ∏ t : Fin h, A (fun i ↦ a i t))
    (project : ∀ h n, M * (Fintype.card J ^ D)^h ≤ n →
      ∃ φ : Projection k (Fin n × Bool) (I × (Fin h → J)),
        φ.hom (map (Int.castRingHom k) (VPVNP.P n)) = forms h)
    (hA : 0 < (F.value (placedTensor place (fun _ ↦ J) A) : ℝ))
    (hgap : ∀ S : Finset I, Fintype.card I ≤ 3 * S.card → 3 * S.card ≤ 2 * Fintype.card I →
      (Fintype.card J : ℝ) ^
        ((D * C : ℕ) * F.wireDistance (centers S false) (centers S true) +
          ∑ i, F.wireDistance (place i) (centers S (cutSide S i))) <
        (F.value (placedTensor place (fun _ ↦ J) A) : ℝ)) :
    ¬ ∀ N, ∃ n ≥ N, circuitSize (map (Int.castRingHom k) (VPVNP.P n)) ≤ n^C := by
  intro small
  let K := (M * Fintype.card J ^ D)^C
  obtain ⟨N, hN⟩ := eventually_no_balanced_power_circuit F place centers A (D*C) K
    (Nat.mul_pos hD hC) hI (by omega) hA hgap
  obtain ⟨h, hn, hs⟩ := arbitrarily_large_powers_of_small_circuits forms hM
    (one_lt_pow₀ hJ hD.ne') project small N
  obtain ⟨c, hc⟩ := circuitSize_spec (forms h)
  refine hN h hn _ ?_ c (fun a ↦ by rw [hc]; exact coeffs h a)
  simpa only [K, ← pow_mul, mul_assoc, mul_comm D h] using hs

end VPVNP
end Computability
end OAI
