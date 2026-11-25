import OAI.Computability.BorderVNP.CubeLabelProducerClock
import OAI.Computability.BorderVNP.CubeLabelResources

/-! # Allocation and word room for the complete contiguous chooser scratch region -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open TeamScales MeanChoice Filter

/-- Lay out labels, heads, paired nodes, demand and both mean arrays consecutively
starting at `base`, above the geometry and delivery producers. -/
def Layout.placed (l : Layout) (base : ℕ) : Layout :=
  let heads := base+l.cells
  let nodes := heads+l.cells
  let data := nodes+8*l.cableCount
  let cableMean := data+l.cells
  {l with heads,nodes,data,cableMean,dataMean := cableMean+l.labels^2}

/-- One-past-end address of the six arrays, including the output labels. -/
def scratchEnd (l : Layout) (base : ℕ) :=
  base+3*l.cells+8*l.cableCount+l.labels^2+l.labels

/-- Contiguous placement satisfies each disjointness requirement of the native initializer. -/
theorem Layout.allocated_placed (l : Layout) (base : ℕ) (cab : l.cables+l.cableCount*3 ≤ base)
    (del : l.deliveries+l.deliveryCount*7 ≤ base) : Allocated (l.placed base) := by
  constructor <;> dsimp only [Layout.placed] <;> (try rw [pow_two]) <;> omega

/-- Word address immediately following the final populated mean array. -/
theorem Layout.placed_end (l : Layout) (base : ℕ) :
    (l.placed base).dataMean+l.labels = scratchEnd l base := by
  unfold placed scratchEnd; ring

/-- Allocation never needs more words than the initializer's clock allowance. -/
theorem scratchEnd_le_init (l : Layout) (base : ℕ) : scratchEnd l base ≤ base+initTicks l := by
  unfold scratchEnd initTicks
  omega

/-- On the manuscript clock the whole chooser region occupies at most `nr` words
after the geometry and input-array high-water address. -/
theorem scratchEnd_le_polynomial (l : Layout) (base d n r z : ℕ) (m : ℕ → ℕ)
    (hn : 1 ≤ n) (hr : 1 ≤ r) (old : base ≤ (2*n*r)^d)
    (clock : (directoryTicks l z m : ℝ) < r*(n:ℝ)^(95/100 : ℝ)) :
    scratchEnd l base ≤ (2*n*r)^(d+2) := by
  let X := 2*n*r
  have two : 2 ≤ X := by
    have hp : 0 < n*r := Nat.mul_pos hn hr
    dsimp [X]; rw [Nat.mul_assoc]; omega
  have hnr : n*r ≤ X := by dsimp [X]; rw [Nat.mul_assoc]; omega
  have pow : (n:ℝ)^(95/100 : ℝ) ≤ n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ (n:ℝ) by exact_mod_cast hn)
      (show (95/100 : ℝ) ≤ 1 by norm_num)
  have cl := clock.le.trans (mul_le_mul_of_nonneg_left pow (Nat.cast_nonneg r))
  have max : directoryTicks l z m ≤ n*r := by rw [mul_comm] at cl; exact_mod_cast cl
  have budget : initTicks l ≤ directoryTicks l z m := Nat.le_add_right ..
  have h₁ : base ≤ X^(d+1) := old.trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))
  have h₂ : n*r ≤ X^(d+1) := hnr.trans (Nat.le_self_pow (by omega) _)
  calc
    scratchEnd l base ≤ base+initTicks l := scratchEnd_le_init ..
    _ ≤ X^(d+1)+X^(d+1) := Nat.add_le_add h₁ ((budget.trans max).trans h₂)
    _ = X^(d+1)*2 := by omega
    _ ≤ X^(d+1)*X := Nat.mul_le_mul_left _ two
    _ = _ := (pow_succ X (d+1)).symm

/-- All allocated addresses and all volume and score words fit simultaneously
from a polynomial producer base and the actual clock and volume bounds. -/
theorem eventually_scratch_word {α ξ : ℝ} (hα : 0 < α) (a : ℕ) (small : α*a < 1/10^6)
    (hξ : 0 ≤ ξ) (B d : ℕ) : ∀ᶠ n : ℕ in atTop, ∀ r R w base z (l : Layout) (m : ℕ → ℕ),
      1 ≤ r → R ≤ n → logWidth r n^2 ≤ w → base ≤ (2*n*r)^d → l.labels = labelCount α a n →
      (directoryTicks l z m : ℝ) < r*(n:ℝ)^(95/100 : ℝ) →
      inputWidth l m ≤ B*(exterior ξ r n*R+1) →
      scratchEnd l base + wordEnvelope l.labels (inputWidth l m) < 2^w := by
  filter_upwards [eventually_envelope hα a small hξ B (d+2),eventually_ge_atTop 1] with n word hn
  intro r R w base z l m hr hR hw old Z clock volume
  rw [Z]
  exact word r R w _ _ hr hR hw (scratchEnd_le_polynomial l base d n r z m hn hr old clock) volume

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
