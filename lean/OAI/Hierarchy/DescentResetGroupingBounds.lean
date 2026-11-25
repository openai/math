import OAI.Hierarchy.DescentResetRateNumbers
import OAI.Hierarchy.DescentGroupingFactor

namespace OAI
/-! # Dyadic grouping for the fixed nonhub reset paths -/

namespace Hierarchy.DescentColonies

/-- Choose the dyadic allowance after the physical largest nonhub route is known. -/
theorem grouping_for_hops (K hops padding : ℕ) (hh : 0<hops) :
    ∃ f : ℕ, padding≤2^f ∧ 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f ≤ 1/(hops:ℝ) := by
  have positive : 0<(hops:ℝ) := by exact_mod_cast hh
  obtain ⟨f,large,small⟩ := choose_grouping_factor (K:ℝ) (1/(hops:ℝ)) (by positivity) padding
  refine ⟨f,large,?_⟩
  simpa only [resetTail,mul_assoc,mul_left_comm,mul_comm] using small

end Hierarchy.DescentColonies

namespace Hierarchy.DescentResetInvoice
open DescentColonies

theorem grouping_for_nonhub (K Δ Y w : ℕ) :
    ∃ f : ℕ, Y^2*w≤2^f ∧
      128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f ≤ 1/(nonhubHops Δ Y:ℝ) :=
  grouping_for_hops K (nonhubHops Δ Y) (Y^2*w) (by unfold nonhubHops; omega)

end Hierarchy.DescentResetInvoice

end OAI
