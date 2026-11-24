import OAI.Computability.VPVNP.BalancedWireLayout
import OAI.Computability.VPVNP.BalancedGrowth
import OAI.Computability.VPVNP.PlacedTensor

/-!
# Tensor powers and the balanced-cut obstruction

The tensor value of an `h`-fold power is the `h`th power of its initial value.
For a polynomial-size circuit, each balanced layout contributes at most a fixed
constant times its own exponential. If every layout has smaller growth than the
initial tensor, no circuit within the given size bound can compute the coefficients
at any sufficiently large power. This is the comparison at the end of Theorem 4.2.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial WireTensor Filter

variable {k : Type*} [Field k] {I J : Type} {P : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype P]

omit [DecidableEq I] in
private theorem bridge_dimension_bound {C K s h : ℕ} (hC : 0 < C)
    (hq : 0 < Fintype.card J) (hs : s ≤ K * (Fintype.card J ^ h) ^ C) :
    Fintype.card (Circuit.BalancedStates I (Fin h → J) s) ≤
      (Fintype.card I * (Fintype.card I + K + 1)) * (Fintype.card J ^ h) ^ C := by
  calc
    _ ≤ Fintype.card I * (Fintype.card I * Fintype.card J ^ h + s + 1) := by
      simpa only [Fintype.card_fun, Fintype.card_fin] using
        Circuit.card_balancedStates_le I (Fin h → J) s
    _ ≤ Fintype.card I *
        (Fintype.card I * (Fintype.card J ^ h)^C + K * (Fintype.card J ^ h)^C +
          (Fintype.card J ^ h)^C) := by
      apply Nat.mul_le_mul_left
      apply Nat.add_le_add
      · apply Nat.add_le_add _ hs
        exact Nat.mul_le_mul_left _ (Nat.le_self_pow hC.ne' _)
      · exact Nat.pow_pos (Nat.pow_pos hq)
    _ = _ := by ring

private theorem power_layout_cost (q M h C : ℕ) (hq : 0 < q) (bridge outer : ℝ) :
    ((M * (q ^ h) ^ C : ℕ) : ℝ) ^ bridge * ((q ^ h : ℕ) : ℝ) ^ outer =
      (M : ℝ) ^ bridge * ((q : ℝ) ^ ((C : ℝ) * bridge + outer)) ^ h := by
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  simp only [Nat.cast_mul, Nat.cast_pow, Real.mul_rpow (Nat.cast_nonneg _) (by positivity : 0 ≤ ((q : ℝ)^h)^C)]
  rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (q : ℝ) ^ h),
    ← Real.rpow_natCast_mul hq'.le, ← Real.rpow_natCast_mul hq'.le,
    mul_assoc, ← Real.rpow_add hq', ← Real.rpow_mul_natCast hq'.le]
  congr 2
  ring

omit [DecidableEq I] in
/-- A placed tensor power has the spectral value of the original coefficient array
raised to the power `h`, with the local digit order explicit. -/
theorem placed_array_power_value (F : SpectralPoint k P) (place : I → P)
    (A : (I → J) → k) (h : ℕ) :
    F.value (placedTensor place (fun _ ↦ Fin h → J)
      (fun a ↦ ∏ t : Fin h, A (fun i ↦ a i t))) =
      F.value (placedTensor place (fun _ ↦ J) A) ^ h :=
  F.value_placed_tensorPowerFin place h
    (Tensor.mk (fun _ : I ↦ J) (fun _ ↦ inferInstance) A)

/-- Finite spectral upper bound on one concrete power. The multiplicative budget
factor `K` remains explicit, so it can also be chosen polynomially in `h`. -/
theorem spectral_power_bound (F : SpectralPoint k P) (place : I → P)
    (centers : Finset I → Bool → P) (A : (I → J) → k) {C K h s : ℕ}
    (hC : 0 < C) (hI : 3 ≤ Fintype.card I) (hJ : 0 < Fintype.card J)
    (hs : s ≤ K * (Fintype.card J ^ h)^C) (c : Circuit k (I × (Fin h → J)) s)
    (hc : ∀ a, c.polynomial.coeff (partyExponent Finset.univ a) = ∏ t : Fin h, A (fun i ↦ a i t)) :
    (F.value (placedTensor place (fun _ ↦ J) A) : ℝ)^h ≤
      ∑ S : Finset I with Fintype.card I ≤ 3*S.card ∧ 3*S.card ≤ 2*Fintype.card I,
        ((Fintype.card I * (Fintype.card I + K + 1) : ℕ) : ℝ) ^
          F.wireDistance (centers S false) (centers S true) *
        ((Fintype.card J : ℝ) ^ ((C : ℝ)*F.wireDistance (centers S false) (centers S true) +
          ∑ i, F.wireDistance (place i) (centers S (cutSide S i))))^h := by
  classical
  let M := Fintype.card I * (Fintype.card I + K + 1)
  have hwidth := bridge_dimension_bound (I := I) hC hJ hs
  have hM : 0 < M := by dsimp [M]; positivity
  have ub := c.spectralValue_le_balanced_cost hI
    (by simpa only [Fintype.card_fun, Fintype.card_fin] using Nat.pow_pos hJ (n := h))
    (Nat.mul_pos hM (Nat.pow_pos (Nat.pow_pos hJ))) hwidth F place centers
  rw [funext hc, placed_array_power_value, NNReal.coe_pow] at ub
  simp only [Fintype.card_fun, Fintype.card_fin] at ub
  apply ub.trans_eq
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  exact power_layout_cost (Fintype.card J) M h C hJ _ _

/-- If every balanced two-center layout costs less than the tensor's spectral value,
all sufficiently large powers violate the indicated gate budget. Only the selected
formal coefficients of the circuit are prescribed. -/
theorem eventually_no_balanced_power_circuit (F : SpectralPoint k P) (place : I → P)
    (centers : Finset I → Bool → P) (A : (I → J) → k) (C K : ℕ)
    (hC : 0 < C) (hI : 3 ≤ Fintype.card I) (hJ : 0 < Fintype.card J)
    (hA : 0 < (F.value (placedTensor place (fun _ ↦ J) A) : ℝ))
    (hgap : ∀ S : Finset I, Fintype.card I ≤ 3 * S.card → 3 * S.card ≤ 2 * Fintype.card I →
      (Fintype.card J : ℝ) ^
        ((C : ℝ) * F.wireDistance (centers S false) (centers S true) +
          ∑ i, F.wireDistance (place i) (centers S (cutSide S i))) <
        (F.value (placedTensor place (fun _ ↦ J) A) : ℝ)) :
    ∃ N : ℕ, ∀ h ≥ N, ∀ s ≤ K * (Fintype.card J ^ h) ^ C, ∀ c : Circuit k (I × (Fin h → J)) s,
      ¬ ∀ a, c.polynomial.coeff (partyExponent Finset.univ a) = ∏ t : Fin h, A (fun i ↦ a i t) := by
  classical
  let cuts := Finset.univ.filter
    (fun S : Finset I ↦ Fintype.card I ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * Fintype.card I)
  let M := Fintype.card I * (Fintype.card I + K + 1)
  let bridge (S : Finset I) := F.wireDistance (centers S false) (centers S true)
  let outer (S : Finset I) := ∑ i, F.wireDistance (place i) (centers S (cutSide S i))
  let base (S : Finset I) := (Fintype.card J : ℝ) ^ ((C : ℝ) * bridge S + outer S)
  let weight (S : Finset I) := (M : ℝ) ^ bridge S
  let v := (F.value (placedTensor place (fun _ ↦ J) A) : ℝ)
  have gap (S : Finset I) (hS : S ∈ cuts) : 0 ≤ base S ∧ base S < v := by
    obtain ⟨lo, hi⟩ := (Finset.mem_filter.mp hS).2
    exact ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, hgap S lo hi⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_weighted_pow_lt cuts weight base v 1 hA zero_lt_one gap)
  refine ⟨N, fun h hn s hs c hc ↦ ?_⟩
  have bound := spectral_power_bound F place centers A hC hI hJ hs c hc
  exact (not_lt_of_ge bound) (by simpa only [one_mul] using hN h hn)

end VPVNP
end Computability
end OAI
