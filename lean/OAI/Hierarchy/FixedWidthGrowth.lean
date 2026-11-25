import OAI.Hierarchy.FixedGraphForcing

namespace OAI
/-! # Absorbing fixed graph error in the growing edge width -/

namespace Hierarchy.FixedWidth

open Filter Real

/-- Real-cast form used when the slot-rank bound is written as a real sum. -/
theorem log_size_le {q K s : ℕ} (hq : 2 ≤ q) (hs : s ≤ q^K) :
    logb 2 ((s:ℝ)+2) ≤ ((K:ℝ)+2)*logb 2 q := by
  simpa using fixedGraph_log_size_le_slope q K s hq hs

/-- A strict gap in the coefficient of the logarithmic load absorbs an
arbitrary fixed multiple of its square root. -/
theorem eventually_absorb {a b E : ℝ} (gap : b < a) :
    ∀ᶠ q : ℕ in atTop, b*logb 2 q + E*sqrt (logb 2 q) < a*logb 2 q := by
  obtain ⟨N,_,bound⟩ := fixedGraph_log_eventually_ge (max 1 ((E/(a-b)+1)^2))
  filter_upwards [eventually_ge_atTop N] with q hq
  have w := bound q hq
  have pos : 0 < logb 2 q := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    ((le_max_left _ _).trans w)
  have root := Real.le_sqrt_of_sq_le ((le_max_right _ _).trans w)
  have ratio : E/(a-b) < sqrt (logb 2 q) := lt_of_lt_of_le (lt_add_one _) root
  have small := (div_lt_iff₀ (sub_pos.mpr gap)).1 ratio
  calc
    b*logb 2 q + E*sqrt (logb 2 q) <
        b*logb 2 q + (sqrt (logb 2 q)*(a-b))*sqrt (logb 2 q) :=
      add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_right small (Real.sqrt_pos.2 pos))
    _ = b*logb 2 q + (a-b)*(sqrt (logb 2 q)*sqrt (logb 2 q)) := by ring
    _ = a*logb 2 q := by rw [Real.mul_self_sqrt pos.le]; ring


end Hierarchy.FixedWidth

end OAI
