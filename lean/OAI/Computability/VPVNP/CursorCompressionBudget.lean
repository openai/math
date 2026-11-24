import OAI.Computability.VPVNP.CompressionBudget
import OAI.Computability.VPVNP.CursorBounds

/-!
# Communication of the routed cursor network after compression

This specialization uses the actual numbers of sites, cursor positions, and
reserved routing bits in Sections 11 and 12. Its remaining inputs concern
an admitted compressor path and the external operations performed on it.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open Filter Asymptotics CursorBounds

/-- Equations (12.1) and the external budget of Proposition 13.1 for the prescribed
cursor network. Its position and width bounds are supplied by the routing construction. -/
theorem cursorPairSimulation_budget (B k : ℕ) {θ δ d c κ C : ℝ}
    (hθ : 0 < θ) (hθ' : θ < 1 / 100) (hδ : δ < θ / 10)
    (hd : 0 ≤ d) (hc : 0 ≤ c) (hκ : 2 < κ) (hC : 0 ≤ C)
    {Wire : ℕ → Type*} [∀ n, Fintype (Wire n)] (width : ∀ n, Wire n → ℕ)
    (mass : ∀ n, Wire n → ℝ) (hmass : ∀ᶠ n in atTop, ∀ e, 0 < mass n e)
    (hnorm : ∀ᶠ n in atTop, ∑ e, mass n e = 1)
    {L : ℕ → ℕ → ℝ} {work : ℕ → ℕ} (hinit : ∀ᶠ n in atTop,
      0 ≤ L n 0 ∧ Real.sqrt (L n 0) ≤ d * initialPositions B n * initialWidth B n)
    (hstep : ∀ᶠ n in atTop, ∀ i < blockCount θ n, L n (i + 1) ≤ L n i / 4 +
      c * ((initialPositions B n : ℝ) / κ ^ i) ^ 2)
    (hfinal : ∀ᶠ n in atTop, ∑ e, (width n e : ℝ) ^ 2 / mass n e ≤ L n (blockCount θ n))
    (hwork : ∀ᶠ n in atTop, (work n : ℝ) ≤ C * (initialPositions B n *
      (n : ℝ) ^ (1 / 100 : ℝ) * (n.log2 + 1 : ℝ) ^ k + ↑(∑ e, width n e))) :
    (∀ᶠ n in atTop, (∑ e, (width n e : ℝ)) ≤ processorCount B n * (n : ℝ) ^ (1 - θ / 2)) ∧
    (fun n => (work n : ℝ)) =o[atTop] (fun n => (processorCount B n : ℝ) * liveBucket δ n) :=
  pairSimulation_budget width mass hmass hnorm hθ hθ' hδ hd hc hκ (by positivity) hC
    ((eventually_ge_atTop 2).mono fun n => initialPositions_bound B n)
    ((eventually_ge_atTop 2).mono fun n => initialWidth_bound B n) hinit hstep hfinal hwork

/-- Fixing the address exponent after the number of lanes per block provides
the lanes, the local field bound, and enough counter bits at the same lengths. -/
theorem cursorResource_bounds (B lanes : ℕ) {θ C₂ A : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hC : 1 ≤ C₂) (hexp : θ * Real.logb 2 C₂ ≤ 1 / 100) (hA : 0 ≤ A)
    (hB : max lanes 5 ≤ B) : ∀ᶠ n : ℕ in atTop,
      lanes * blockCount θ n ≤ virtualBits B n ∧
      A * C₂ ^ blockCount θ n * (initialWidth B n + 1 : ℝ) ≤ (n : ℝ) ^ (3 / 10 : ℝ) ∧
      (initialPositions B n : ℝ) * (n : ℝ) ^ (1 / 100 : ℝ) * (n : ℝ) ^ (2 / 5 : ℝ) <
        (processorCount B n : ℝ) ^ 2 := by
  have hlen := eventually_fieldGrowth_le (B := 56 * ((B : ℝ) + 3) ^ 2 * ((B : ℝ) + 10) ^ 4)
    hθ hC hexp hA 6
  have hcounter := eventually_counter_lt (2 * ((B : ℝ) + 2)) 2
  filter_upwards [eventually_ge_atTop 3, hlen, hcounter] with n hn hlen hcounter
  have hn' : 2 ≤ n := by omega
  exact ⟨by simpa [Nat.mul_comm] using laneBudget B lanes n (le_trans (le_max_left _ _) hB) hθ' hn,
    (hlen _ (initialWidth_bound B n hn')).1,
    hcounter _ _ (pow_five_le_processorCount n (le_trans (le_max_right _ _) hB))
      (initialPositions_bound B n hn')⟩

end Compression

end VPVNP
end Computability
end OAI
