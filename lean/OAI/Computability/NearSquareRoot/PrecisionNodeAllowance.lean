import OAI.Computability.NearSquareRoot.PrecisionWalshWidth
import OAI.Computability.NearSquareRoot.PrecisionGrid

/-! # Guarded budgets down the logarithmic recursive depth -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open Filter FixedPoint

/-- A constant raised to the recursion depth is polynomial in the active
address width. Its logarithm is absorbed by one full address-width guard. -/
theorem eventually_depthAllowance (C : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ j : ℕ, 2^j ≤ k → (C : ℝ)^(j+1) ≤ (2 : ℝ)^k := by
  filter_upwards [eventually_polynomial_le_array_length (C:ℝ) (by positivity) C] with k hk
  intro j hj
  have hC : (C : ℝ) ≤ (2:ℝ)^C := by exact_mod_cast (Nat.le_of_lt Nat.lt_two_pow_self)
  have hJ : (2 : ℝ)^j ≤ (k : ℝ) := by exact_mod_cast hj
  calc
    (C:ℝ)^(j+1) = C * (C:ℝ)^j := pow_succ' ..
    _ ≤ C * ((2:ℝ)^C)^j := by gcongr
    _ = C * ((2:ℝ)^j)^C := by rw [← pow_mul, Nat.mul_comm C j, pow_mul]
    _ ≤ C*(1+(k:ℝ))^C := by gcongr; linarith
    _ ≤ _ := hk

noncomputable def unitFault (k : ℕ) : ℝ := Real.sqrt ((2:ℝ)^k) * (2/2^fractionBits k)

theorem unitFault_nonneg (k : ℕ) : 0 ≤ unitFault k := by unfold unitFault; positivity

/-- The accumulated error of one recursive piece fits well inside the
per-transform error budget, including the square-root-of-volume factor. -/
theorem depthFault {C k j : ℕ} (h : (C:ℝ)^(j+1) ≤ (2:ℝ)^k) :
    (C:ℝ)^(j+1)*unitFault k ≤ 1/(2:ℝ)^(68*k) := by
  have hs : Real.sqrt ((2:ℝ)^k) ≤ 2^k :=
    Real.sqrt_le_self_iff.mpr (.inr (one_le_pow₀ (by norm_num)))
  have he : fractionBits k = 68*k+k+k+1 := by unfold fractionBits; omega
  calc
    _ ≤ (2:ℝ)^k * ((2:ℝ)^k * (2/2^fractionBits k)) := by unfold unitFault; gcongr
    _ = _ := by rw [he,pow_succ,pow_add,pow_add]; field_simp

/-- The root has enough headroom for all recursively reached lanes. -/
theorem depthRoom {C k j : ℕ} (hk : 1 ≤ k) (h : (C:ℝ)^(j+1) ≤ (2:ℝ)^k) {M : ℝ}
    (hM : 0 ≤ M) (hm : M ≤ (2:ℝ)^(13*k)) :
    (C:ℝ)^(j+1)*(M+1) ≤ (2:ℝ)^(20*k) := by
  calc
    _ ≤ (2:ℝ)^k * ((2:ℝ)^(13*k) + 1) := by gcongr
    _ ≤ (2:ℝ)^k * ((2:ℝ)^(13*k) * 2) := by
      gcongr; linarith [one_le_pow₀ (by norm_num : 1 ≤ (2:ℝ)) (n := 13*k)]
    _ = (2:ℝ)^(k+13*k+1) := by rw [pow_succ,pow_add]; ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)

theorem gridRoom (k : ℕ) : (2:ℝ)^(20*k)*2^fractionBits k < 2^componentBits k := by
  rw [← pow_add]
  exact (pow_lt_pow_right₀ (by norm_num : 1 < (2:ℝ))) (by unfold fractionBits componentBits; omega)

/-- The child headroom cannot exceed the global storage cap. -/
theorem nextCap_le {T R : ℝ} (hT : 0 ≤ T) (hR : 1 ≤ R) : T/R-1 ≤ T := by
  have h := div_le_self hT hR
  linarith

theorem nextCap_child {T R M : ℝ} (hR : 0 < R) (h : M ≤ T/R-1) : R*(M+1) ≤ T := by
  rw [mul_comm, ← le_div_iff₀ hR]
  linarith

/-- Budgeting a complete template leaves one additional unit for its child's
own guard; this keeps the headroom recurrence multiplicative in the depth. -/
theorem nextCap_plan {T R C F M δ : ℝ} (hR : 0 < R) (hF : 0 ≤ F) (hM : 0 ≤ M)
    (hδ : δ ≤ 1) (hC : F+1 ≤ C) (h : R*C*(M+1) ≤ T) :
    F*(M+δ) ≤ T/R-1 := by
  have h1 : F*(M+δ)+1 ≤ C*(M+1) := by
    nlinarith [mul_nonneg hF (sub_nonneg.mpr hδ), mul_nonneg (sub_nonneg.mpr hC) hM]
  have h2 : C*(M+1) ≤ T/R := (le_div_iff₀ hR).mpr (by linarith only [h])
  linarith

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
