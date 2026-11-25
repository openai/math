import OAI.Computability.NearSquareRoot.FixedLayerClock
import OAI.Computability.NearSquareRoot.FixedCandidateFrame
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetTotal

/-! # Charging actual permutation records and total row profiles to the input width -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedPermutationBudget
open Filter IntegerMultiplication FixedCandidate DigitPacking FixedLayer

/-- Number of data slots in the native row allowance for a complete complex grid array. -/
def gridVolume (n : ℕ) := 2^(addressBits n)*(384*addressBits n+23)

/-- Includes the leading sentinel allowance for each of the fixed-precision Gaussian records. -/
theorem gridVolume_le {n : ℕ} (hn : 2 ≤ n) : gridVolume n ≤ 73728*n := by
  have shape := array_volume hn
  calc
    gridVolume n ≤ (DigitPacking.capacity n+1)*(384*(addressBits n+1)) :=
      Nat.mul_le_mul (Nat.le_succ _) (by omega)
    _ = 384*((DigitPacking.capacity n+1)*(addressBits n+1)) := by ring
    _ ≤ 384*(192*n) := Nat.mul_le_mul_left _ shape
    _ = _ := by ring

/-- An integer coefficient on volume carries through the rounded physical clock. -/
theorem layerClock_volume {V n C : ℕ} (bound : V ≤ C*n) (ρ : ℝ) (k : ℕ) :
    layerClock ρ k V ≤ C*layerClock ρ k n := by
  apply Nat.ceil_le.mpr
  push_cast
  have h : (V:ℝ) ≤ (C:ℝ)*n := by exact_mod_cast bound
  calc
    _ ≤ ((C:ℝ)*n)*(1+(k:ℝ))^ρ := mul_le_mul_of_nonneg_right h (by positivity)
    _ = (C:ℝ)*((n:ℝ)*(1+(k:ℝ))^ρ) := mul_assoc ..
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _)

/-- One directed global permutation layer at its actual padded-record width. -/
theorem grid_rowClock {ρ : ℝ} (hr : 0 ≤ ρ) :
    RowClock ρ (fun n => layerClock ρ (addressBits n) (gridVolume n)) := by
  obtain ⟨B,pos,l,cost⟩ := permutationClock_bound hr
  refine ⟨73728*B,by positivity,l,?_⟩
  filter_upwards [cost,eventually_ge_atTop (2:ℕ)] with n hc hn
  have base := layerClock_volume (gridVolume_le hn) ρ (addressBits n)
  calc
    _ ≤ (73728:ℝ)*(layerClock ρ (addressBits n) n:ℝ) := by exact_mod_cast base
    _ ≤ 73728*integerBudget B 0 ρ l 0 n := mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = _ := by unfold integerBudget; ring

/-- Evaluate the proof-only total profile of the generated command at a good tuple.
The resulting row class is closed under the chronological directed layer sweep. -/
theorem profile_rowClock {P : Type*} (arena clock target : P → ℕ → ℕ) (cut : P → ℕ)
    {p : P} {ρ : ℝ} (hr : 0 ≤ ρ) (targetClock : RowClock ρ (target p))
    (profile : ∀ w ≥ cut p, arena p w = w ∧ clock p w = max w (target p w)) :
    (∀ᶠ n in atTop, arena p n = n) ∧ RowClock ρ (clock p) := by
  have sum := (RowClock.linear hr).add targetClock
  obtain ⟨B,hB,l,fit⟩ := sum
  refine ⟨(eventually_ge_atTop (cut p)).mono fun n hn => (profile n hn).1, B,hB,l,?_⟩
  filter_upwards [fit,eventually_ge_atTop (cut p)] with n h hn
  rw [(profile n hn).2]
  apply le_trans _ h
  exact_mod_cast (show max n (target p n) ≤ n+target p n by omega)

end SynchronizedPermutationBudget

end NearSquareRoot
end Computability
end OAI
