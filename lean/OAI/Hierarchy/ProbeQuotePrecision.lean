import OAI.Hierarchy.ProbePublicTimes

namespace OAI
/-! # Shared finite precision for the price and discrepancy ROMs in the entire catalogue -/

namespace Hierarchy.AdaptiveProbe
noncomputable section

/-- A single positive integer serves both downward roundings and pays the full
quote error on every possible committed histogram. `lanes` also covers the score
check's one-eighth allowance across the entire public commodity alphabet. -/
theorem quote_precision (roles maxWidth lanes : ℕ) {failure γ : ℝ} (ht : 0<failure) (hg : 0<γ) :
    ∃ Q : ℕ, 0<Q ∧ 8*lanes≤Q ∧ 1/(Q:ℝ)+1/(Q:ℝ)≤failure ∧
      ∀ e m b : ℕ,e≤roles → m≤maxWidth → 0<b →
      (e:ℝ)*m*(1/(Q:ℝ))≤(b:ℝ)*γ/2 := by
  let lim := max (2/failure) (2*(roles:ℝ)*maxWidth/γ)
  obtain ⟨q,more⟩ := exists_nat_gt lim
  let Q := max (8*lanes) q
  have hi : (q:ℝ)≤Q := by exact_mod_cast (le_max_right (8*lanes) q)
  have first := (le_max_left (2/failure) (2*(roles:ℝ)*maxWidth/γ)).trans (more.le.trans hi)
  have second := (le_max_right (2/failure) (2*(roles:ℝ)*maxWidth/γ)).trans (more.le.trans hi)
  have hp : 0<(Q:ℝ) := (by positivity : 0<(2:ℝ)/failure).trans_le first
  have tol := (div_le_iff₀ ht).mp first
  have pair := (div_le_iff₀ hg).mp second
  refine ⟨Q,Nat.cast_pos.mp hp,le_max_left ..,?_,?_⟩
  · rw [←add_div,div_le_iff₀ hp]; linarith
  · intro e m b er mr bp
    have eb : (e:ℝ)*m≤roles*maxWidth := mul_le_mul (Nat.cast_le.mpr er) (Nat.cast_le.mpr mr) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have one : (1:ℝ)≤b := by exact_mod_cast bp
    have small : (e:ℝ)*m*(1/(Q:ℝ))≤γ/2 := by
      rw [mul_one_div,div_le_iff₀ hp]
      linarith only [eb,pair]
    exact small.trans (div_le_div_of_nonneg_right ((one_mul γ).symm.le.trans (mul_le_mul_of_nonneg_right one hg.le)) (by norm_num))

end
end Hierarchy.AdaptiveProbe

end OAI
