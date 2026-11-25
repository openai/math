import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Tactic

/-!
# Rounding across a sequence of unitary transform layers

The local accuracy of a represented layer need only hold inside its working
range. The induction bounds all represented boundary norms and hence licenses
the local estimate for the next invocation. Forward and adjoint transforms use
the same estimate.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

variable {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Value of a stream after a prefix of the exact layers. -/
def exactLayerPrefix (U : ℕ → E →ₗᵢ[𝕜] E) (x : E) : ℕ → E
  | 0 => x
  | j + 1 => U j (exactLayerPrefix U x j)

theorem norm_exactLayerPrefix (U : ℕ → E →ₗᵢ[𝕜] E) (x : E) (j : ℕ) :
    ‖exactLayerPrefix U x j‖ = ‖x‖ := by
  induction j with
  | zero => rfl
  | succ j ih => simpa only [exactLayerPrefix, LinearIsometry.norm_map] using ih

/-- Error grows by at most one local tolerance per executed layer. The
hypothesis on a rounded step applies only when its input norm is in range. -/
theorem roundedLayerPrefix_bound (U : ℕ → E →ₗᵢ[𝕜] E) (v : ℕ → E) (m : ℕ)
    {δ R : ℝ} (hδ : 0 ≤ δ) (hR : ‖v 0‖ + m * δ ≤ R)
    (hstep : ∀ j < m, ‖v j‖ ≤ R → ‖v (j + 1) - U j (v j)‖ ≤ δ)
    {j : ℕ} (hj : j ≤ m) :
    ‖v j - exactLayerPrefix U (v 0) j‖ ≤ j * δ ∧ ‖v j‖ ≤ R := by
  induction j with
  | zero =>
    simpa [exactLayerPrefix] using
      (show ‖v 0‖ ≤ R by linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) hδ])
  | succ j ih =>
    obtain ⟨herr, hin⟩ := ih (by omega)
    have hprev :
        ‖U j (v j) - U j (exactLayerPrefix U (v 0) j)‖ ≤ j * δ := by
      rwa [← map_sub, LinearIsometry.norm_map]
    have hnew : ‖v (j + 1) - exactLayerPrefix U (v 0) (j + 1)‖ ≤ (j + 1 : ℕ) * δ := by
      calc
        _ ≤ ‖v (j + 1) - U j (v j)‖ +
            ‖U j (v j) - U j (exactLayerPrefix U (v 0) j)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ δ + j * δ := add_le_add (hstep j (by omega) hin) hprev
        _ = ((j + 1 : ℕ) : ℝ) * δ := by push_cast; ring
    refine ⟨hnew, ?_⟩
    calc
      ‖v (j + 1)‖ ≤ ‖v (j + 1) - exactLayerPrefix U (v 0) (j + 1)‖ +
          ‖exactLayerPrefix U (v 0) (j + 1)‖ := norm_le_norm_sub_add _ _
      _ ≤ ((j + 1 : ℕ) : ℝ) * δ + ‖v 0‖ := by
        rw [norm_exactLayerPrefix]
        exact add_le_add hnew le_rfl
      _ ≤ R := by
        have hcast : ((j + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hj
        linarith [mul_le_mul_of_nonneg_right hcast hδ]

/-- The manuscript's precision budget for either transform, including every
intermediate layer boundary. The depth hypothesis is a coarse upper bound
for the synchronized schedule. -/
theorem transformLayerPrecision (U : ℕ → E →ₗᵢ[𝕜] E) (v : ℕ → E) {k m : ℕ}
    (hk : 1 ≤ k) (hm : m ≤ 2 ^ (10 * k))
    (hv : ‖v 0‖ ≤ (2 : ℝ) ^ (12 * k))
    (hstep : ∀ j < m, ‖v j‖ ≤ (2 : ℝ) ^ (13 * k) →
      ‖v (j + 1) - U j (v j)‖ ≤ 1 / (2 : ℝ) ^ (50 * k))
    {j : ℕ} (hj : j ≤ m) :
    ‖v j - exactLayerPrefix U (v 0) j‖ ≤ 1 / (2 : ℝ) ^ (40 * k) ∧
      ‖v j‖ ≤ (2 : ℝ) ^ (13 * k) := by
  have htotal : (m : ℝ) * (1 / 2 ^ (50 * k)) ≤ 1 / 2 ^ (40 * k) := by
    have hmc : (m : ℝ) ≤ 2 ^ (10 * k) := by exact_mod_cast hm
    calc
      _ ≤ (2 : ℝ) ^ (10 * k) * (1 / 2 ^ (50 * k)) :=
        mul_le_mul_of_nonneg_right hmc (by positivity)
      _ = 1 / 2 ^ (40 * k) := by
        rw [show 50 * k = 10 * k + 40 * k by omega, pow_add]
        field_simp
  have hone : (1 : ℝ) ≤ 2 ^ (12 * k) := one_le_pow₀ (by norm_num)
  have htwo : (2 : ℝ) ≤ 2 ^ k := by
    simpa using (pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) hk)
  have hslack : (1 : ℝ) / 2 ^ (40 * k) ≤ 1 := by
    exact (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hR : ‖v 0‖ + m * (1 / (2 : ℝ) ^ (50 * k)) ≤ 2 ^ (13 * k) := by
    rw [show 13 * k = 12 * k + k by omega, pow_add]
    linarith [mul_le_mul_of_nonneg_left htwo (by positivity : 0 ≤ (2 : ℝ) ^ (12 * k))]
  obtain ⟨he, hr⟩ := roundedLayerPrefix_bound U v m (by positivity) hR hstep hj
  have hjc : (j : ℝ) ≤ m := by exact_mod_cast hj
  exact ⟨(he.trans (mul_le_mul_of_nonneg_right hjc (by positivity))).trans htotal, hr⟩

end NearSquareRoot
end Computability
end OAI
