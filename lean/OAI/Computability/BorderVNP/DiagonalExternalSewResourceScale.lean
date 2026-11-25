import OAI.Computability.BorderVNP.DiagonalExternalSewGroupedBudget
import OAI.Computability.BorderVNP.PackedResources

/-! # Absorbing the post-sew local records in the physical §7.3 budgets -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open TeamScales Packing Filter

/-- Even charging all previous public records once for each copy in the
bottom group fits the required public-record exponent. -/
theorem eventually_public_sewn {α τ C : ℝ} (hα : α < 1/1000) (hτ : 0 ≤ τ) (hC : 1 ≤ C)
    (growth : τ*Real.logb 2 C ≤ α/10) (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop, 5*(width n α : ℝ)*(A*C^(epochs τ n)*width n α) ≤ width n (1/100) := by
  have goal := eventually_le_rounded_width (show α/10+α+α < 1/100 by linarith)
    (by norm_num) (by norm_num : (0:ℝ) < 1) (5*A)
  filter_upwards [goal,eventually_ge_atTop 1] with n hn hn1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
  have he := epoch_growth_le hC hn1 hτ growth
  have hw : (width n α : ℝ) ≤ (n : ℝ)^α := Nat.floor_le (Real.rpow_nonneg hn0.le _)
  calc
    _ = (5*A)*(C^(epochs τ n)*(width n α : ℝ)*(width n α : ℝ)) := by ring
    _ ≤ (5*A)*((n : ℝ)^(α/10)*(n : ℝ)^α*(n : ℝ)^α) := by gcongr
    _ = (5*A)*(n : ℝ)^(α/10+α+α) := by rw [Real.rpow_add hn0,Real.rpow_add hn0]
    _ ≤ _ := by simpa only [one_mul] using hn

/-- On the same processor-length regime, the final cost factors for public
and expanded records preserve both rounded thresholds of Proposition 7.2. -/
theorem eventually_sewn_resources {α τ C : ℝ} {K : ℕ} (hα : α < 1/1000) (hτ : 0 < τ)
    (ht : τ < α/100) (hk : 1 ≤ K) (hteam : τ*Real.logb 2 K ≤ α)
    (hC : 1 ≤ C) (growth : τ*Real.logb 2 C ≤ α/10) (d : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ n : ℕ in atTop,
      ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n : ℝ)^ω) →
      ∀ (oldPublic oldExpanded : ℕ),
      (oldPublic : ℝ) ≤ A*C^(epochs τ n)*width n α →
      (oldExpanded : ℝ) ≤ A*C^(epochs τ n)*width n α*(n : ℝ)^(1/10+τ/20)*(logWidth r n : ℝ)^d →
      5*width n α*oldPublic ≤ width n (1/100) ∧ 7*oldExpanded ≤ width n (1/5) := by
  obtain ⟨ω,hω,resource⟩ := eventually_sparse_resources hα hτ ht hk hteam hC growth d
  refine ⟨ω,hω,fun A hA => ?_⟩
  filter_upwards [resource (7*A) (by positivity),eventually_public_sewn hα hτ.le hC growth A hA] with n hmass hpub
  intro r hr room pub mass hp hm
  constructor
  · exact_mod_cast (calc
      5*(width n α : ℝ)*(pub : ℝ) ≤ 5*(width n α : ℝ)*(A*C^(epochs τ n)*width n α) := by gcongr
      _ ≤ _ := hpub)
  · exact_mod_cast (calc
      7*(mass : ℝ) ≤ 7*(A*C^(epochs τ n)*width n α*(n : ℝ)^(1/10+τ/20)*(logWidth r n : ℝ)^d) := by gcongr
      _ = _ := by ring
      _ ≤ (width n (1/5) : ℝ) := (hmass r hr room).1)

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
