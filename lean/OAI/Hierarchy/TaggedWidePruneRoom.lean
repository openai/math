import OAI.Hierarchy.TaggedWidePoolPrice
import OAI.Hierarchy.ProtocolRAMPruneFlag

namespace OAI
/-! # No wraparound in the selected native integer-pruning calculation -/

noncomputable section
namespace Hierarchy.Tagged
open Filter TaggedPrune ProtocolRAM ProtocolRAMEmit
open scoped BigOperators

/-- Upper width interval, actual row footprint, bounded terminal route load,
and physical catalyst reserve suffice uniformly for both integer comparisons.
The negative part of the rational pruning threshold is truncated by native
natural subtraction. -/
theorem eventually_pruning_fits (A : ℝ) (hA : 0≤A) (E N B code M den : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀ {w W k edges : ℕ} {b : Fin k→ℕ}
      (D : Layout h w b) (rows : Fin edges→ProtocolRAMEmit.Row),
      2*h+1≤W → (w:ℝ)≤(2*(h:ℝ))^A → edges≤E*2^h →
      (∀i,(rows i).lengthCode≤code) → (∀i,(rows i).width≤B*w) → (∑j,b j)≤N*2^h*w →
      (∑i,PruneFlag.charge D (rows i))<2^W ∧ 2*M*(∑j,b j)*den-2^h*w*den<2^W := by
  let C := max (E*code*B) (2*M*N*den)
  filter_upwards [eventually_word_room (C:ℝ) A hA] with h store
  intro w W k edges b D rows word payload size codes widths reserve
  have fit (v : ℕ) (amount : v≤C*2^h*w) : v<2^W := by
    apply (store v ?_).trans_le (Nat.pow_le_pow_right (by decide) word)
    have vr : (v:ℝ)≤(C:ℝ)*(2:ℝ)^h*(w:ℝ) := by exact_mod_cast amount
    calc
      _ ≤ (C:ℝ)*(2:ℝ)^h*(2*(h:ℝ))^A := vr.trans (mul_le_mul_of_nonneg_left payload (by positivity))
      _ = _ := by ring
  constructor
  · apply fit
    calc
      _ ≤ edges*(code*(B*w)) := PruneFlag.sum_charge_le D rows code (B*w) codes widths
      _ ≤ (E*2^h)*(code*(B*w)) := Nat.mul_le_mul_right _ size
      _ = (E*code*B)*2^h*w := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_max_left ..))
  · apply fit
    calc
      _ ≤ 2*M*(∑j,b j)*den := Nat.sub_le _ _
      _ ≤ 2*M*(N*2^h*w)*den := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ reserve)
      _ = (2*M*N*den)*2^h*w := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_max_right ..))

end Hierarchy.Tagged

end
end OAI
