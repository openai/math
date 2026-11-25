import OAI.Computability.BorderVNP.CrossingSplitRate
import OAI.Computability.BorderVNP.CrossingFusionEnergy
import OAI.Computability.VPVNP.PolynomialBounds

/-!
# Fitting signed crossing programs into the universal clocked input

The query interpreter accepts a literal program prefix, fixed padding and payload at
every length above its resource estimate. A polynomial bound in the alphabet
cardinality `q=2^m` therefore permits one positive constant `c₁` in `m=⌊c₁ log₂ n⌋`,
uniformly over the choice of side and its coefficient field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open Filter

/-- The bit width grows without bound along the selected input lengths. -/
theorem tendsto_width {c : ℝ} (hc : 0 < c) : Tendsto (width c) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp (((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
    tendsto_natCast_atTop_atTop).const_mul_atTop hc)

/-- The full table of initial wire labels can be stored using only polynomially
many entries in the fresh wire alphabet. Final occupation states use the rank circuit
instead, since their energy is the much larger `D H`. -/
theorem eventually_initial_table_le :
    ∀ᶠ m : ℕ in atTop, stateCountAt (leastEnergy m) ≤ (2^m)^2 ∧ 2 * leastEnergy m ≤ 2^m := by
  have hlim := (stateCountAt_limit.comp leastEnergy_atTop).mul leastEnergy_sqrt_rate
  rw [mul_inv_cancel₀ countExponent_pos.ne'] at hlim
  filter_upwards [hlim.eventually_lt_const (by norm_num : (1 : ℝ) < 2),
    eventually_gt_atTop (0 : ℕ)] with m h hm
  have hs : Real.sqrt (leastEnergy m) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast (leastEnergy_spec m).1)).ne'
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have he : Real.logb 2 (stateCountAt (leastEnergy m)) / m < 2 := by
    simpa only [Function.comp_apply, div_mul_div_cancel₀ hs] using h
  have hq : (0 : ℝ) < stateCountAt (leastEnergy m) := by exact_mod_cast VPVNP.Crossing.cutoffCount_pos _
  have hl := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hq).mp
    ((div_lt_iff₀ hm').mp he).le
  have hb : stateCountAt (leastEnergy m) ≤ (2^m)^2 := by
    rw [mul_comm (2 : ℝ), ← Nat.cast_ofNat (R := ℝ) (n := 2), ← Nat.cast_mul, Real.rpow_natCast,
      pow_mul] at hl
    exact_mod_cast hl
  refine ⟨hb, ?_⟩
  have hc := (leastEnergy_spec m).2.trans_le hb
  rw [pow_two] at hc
  exact le_of_lt (Nat.lt_of_mul_lt_mul_right hc)

/-- An eventual exponential bound on input bits as a function of the width can be
paid at the single source length `n`, with a constant fixed before `n`. -/
theorem fits_source_length {bits : ℕ → ℕ} {a : ℕ}
    (hbits : ∀ᶠ m : ℕ in atTop, bits m ≤ 2^(a*m)) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ᶠ n : ℕ in atTop, bits (width c n) ≤ n := by
  let c : ℝ := 1 / (a+1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by dsimp [c]; rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) a]
  refine ⟨c, hc, hc1, ?_⟩
  filter_upwards [(tendsto_width hc).eventually hbits, eventually_ge_atTop (1 : ℕ)] with n h hn
  apply h.trans
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let x := Real.logb 2 n
  have hx : 0 ≤ x := Real.logb_nonneg (by norm_num) hn'
  have hm : (width c n : ℝ) ≤ c*x := Nat.floor_le (mul_nonneg hc.le hx)
  have ha : (a : ℝ) * c ≤ 1 := by
    dsimp [c]
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  have hcap : (a : ℝ) * width c n ≤ x := by
    calc
      _ ≤ a * (c*x) := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg a)
      _ ≤ 1*x := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right ha hx
      _ = _ := one_mul _
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hcap
  change (2 : ℝ)^((a : ℝ) * width c n) ≤ 2^(Real.logb 2 n) at hpow
  rw [Real.rpow_logb (by norm_num) (by norm_num) (zero_lt_one.trans_le hn'),
    ← Nat.cast_mul, Real.rpow_natCast] at hpow
  exact_mod_cast hpow

/-- A polynomial bound on the prefix and free bits in `q` gives the uniform choice of
`c₁` required on PDF page 12. This applies to any uniform upper bound for the side programs. -/
theorem fits_source_length_of_polynomial {f bits : ℕ → ℕ}
    (hf : VPVNP.PolynomiallyBounded f) (hbits : ∀ᶠ m : ℕ in atTop, bits m ≤ f (2^m)) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ᶠ n : ℕ in atTop, bits (width c n) ≤ n := by
  obtain ⟨A,d,N,h⟩ := hf
  apply fits_source_length (a := d+1)
  filter_upwards [hbits, eventually_ge_atTop (max A N)] with m hm hmax
  have hpower : m ≤ 2^m := (Nat.lt_two_pow_self).le
  have hA : A ≤ 2^m := ((le_max_left ..).trans hmax).trans hpower
  have hN : N ≤ 2^m := ((le_max_right ..).trans hmax).trans hpower
  calc
    _ ≤ A * (2^m)^d := hm.trans (h _ hN)
    _ ≤ 2^m * (2^m)^d := Nat.mul_le_mul_right _ hA
    _ = _ := by rw [← pow_mul, Nat.add_mul, Nat.one_mul, Nat.mul_comm d m, pow_add, Nat.mul_comm]

end Crossing

end BorderVNP
end Computability
end OAI
