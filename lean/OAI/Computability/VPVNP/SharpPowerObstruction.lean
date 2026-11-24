import OAI.Computability.VPVNP.BalancedPowerObstruction
import OAI.Computability.VPVNP.SharpPowerLengths
import OAI.Computability.VPVNP.PolynomialPowerGap

/-!
# Balanced layout comparison with polynomial overhead in the power

An encoding of length `A * (h+1)^D * q^h` gives the central wire exponent `C`
when the source circuit budget is `n^C`. The polynomial in `h` can be retained
as a common factor in the finite sum, since each bridge distance is at most one.
The strict layout gap absorbs this factor at all sufficiently large powers.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial WireTensor Filter

private theorem bridge_overhead_le (ℓ K m : ℕ) (hm : 1 ≤ m) {d : ℝ}
    (h₀ : 0 ≤ d) (h₁ : d ≤ 1) :
    ((ℓ * (ℓ + K * m + 1) : ℕ) : ℝ)^d ≤
      (m : ℝ) * ((ℓ * (ℓ + K + 1) : ℕ) : ℝ)^d := by
  have hnat : ℓ * (ℓ + K*m + 1) ≤ (ℓ*(ℓ+K+1))*m := by
    rw [mul_assoc, add_mul, add_mul, one_mul]
    exact Nat.mul_le_mul_left ℓ (Nat.add_le_add
      (Nat.add_le_add_right (Nat.le_mul_of_pos_right _ (by omega)) _) hm)
  calc
    _ ≤ ((((ℓ*(ℓ+K+1))*m : ℕ) : ℝ))^d := Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast hnat) h₀
    _ = ((ℓ * (ℓ + K + 1) : ℕ) : ℝ)^d * (m : ℝ)^d := by
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    _ ≤ _ := by
      rw [mul_comm (m : ℝ)]
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le (by exact_mod_cast hm) h₁)
      positivity

variable {k : Type*} [Field k] {I J : Type} {P : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype P]

/-- The source budget exponent enters the layout cost unchanged when the
projection length is linear in the terminal dimension up to polynomial factors in
the power `h`. -/
theorem not_small_universal_of_sharp_projections (F : SpectralPoint k P)
    (place : I → P) (centers : Finset I → Bool → P) (A : (I → J) → k)
    (forms : (h : ℕ) → MvPolynomial (I × (Fin h → J)) k) (M D C : ℕ)
    (hM : 0 < M) (hC : 0 < C) (hI : 3 ≤ Fintype.card I) (hJ : 1 < Fintype.card J)
    (coeffs : ∀ h a, (forms h).coeff (partyExponent Finset.univ a) =
      ∏ t : Fin h, A (fun i ↦ a i t))
    (project : ∀ h n, M * (h+1)^D * Fintype.card J^h ≤ n →
      ∃ φ : Projection k (Fin n × Bool) (I × (Fin h → J)),
        φ.hom (map (Int.castRingHom k) (VPVNP.P n)) = forms h)
    (hA : 0 < (F.value (placedTensor place (fun _ ↦ J) A) : ℝ))
    (hgap : ∀ S : Finset I, Fintype.card I ≤ 3*S.card → 3*S.card ≤ 2*Fintype.card I →
      (Fintype.card J : ℝ) ^
        ((C : ℝ) * F.wireDistance (centers S false) (centers S true) +
          ∑ i, F.wireDistance (place i) (centers S (cutSide S i))) <
        (F.value (placedTensor place (fun _ ↦ J) A) : ℝ)) :
    ¬ ∀ N, ∃ n ≥ N, circuitSize (map (Int.castRingHom k) (VPVNP.P n)) ≤ n^C := by
  classical
  intro small
  let cuts := Finset.univ.filter
    (fun S : Finset I ↦ Fintype.card I ≤ 3*S.card ∧ 3*S.card ≤ 2*Fintype.card I)
  let bridge (S : Finset I) := F.wireDistance (centers S false) (centers S true)
  let outer (S : Finset I) := ∑ i, F.wireDistance (place i) (centers S (cutSide S i))
  let base (S : Finset I) := (Fintype.card J : ℝ) ^ ((C : ℝ) * bridge S + outer S)
  let K := (M*Fintype.card J)^C
  let ℓ := Fintype.card I
  let weight (S : Finset I) := ((ℓ*(ℓ+K+1) : ℕ) : ℝ) ^ bridge S
  let v := (F.value (placedTensor place (fun _ ↦ J) A) : ℝ)
  have hw (S : Finset I) (_ : S ∈ cuts) : 0 ≤ weight S :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hb (S : Finset I) (hS : S ∈ cuts) : 0 ≤ base S ∧ base S < v := by
    obtain ⟨lo, hi⟩ := (Finset.mem_filter.mp hS).2
    exact ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, hgap S lo hi⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_polynomial_weighted_pow_lt_target cuts weight base v (D*C) hA hw hb)
  obtain ⟨h, hn, hs⟩ := arbitrarily_large_powers_of_sharp_projections forms hM hJ project small N
  obtain ⟨c, hc⟩ := circuitSize_spec (forms h)
  have bound := spectral_power_bound F place centers A hC hI (by omega) hs c
    (fun a ↦ by rw [hc]; exact coeffs h a)
  apply (not_lt_of_ge (bound.trans ?_)) (hN h hn)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  let m := (h+2)^(D*C)
  have hm : 1 ≤ m := by exact Nat.pow_pos (by omega)
  have hbridge := bridge_overhead_le ℓ K m hm
    (F.wireDistance_nonneg (centers S false) (centers S true))
    (F.wireDistance_le_one (centers S false) (centers S true))
  have castm : (m : ℝ) = ((h : ℝ)+2)^(D*C) := by simp [m]
  rw [castm] at hbridge
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hbridge
    (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (Fintype.card J))
      ((C : ℝ)*bridge S + outer S)) h)

end VPVNP
end Computability
end OAI
