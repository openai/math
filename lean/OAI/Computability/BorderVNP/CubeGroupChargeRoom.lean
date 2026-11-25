import OAI.Computability.BorderVNP.CubePhysicalPaddingBalance
import OAI.Computability.BorderVNP.CubeScales

/-! # Room for group communication at the rounded team scales

Rounding the packet capacity costs at most one block per ordered label pair.
The alphabet absorbs the fixed per-packet expansion and the number of teams,
while the exterior width absorbs the private description and the two possible literal fields.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Filter TeamScales

/-- One processor on one team already supplies half the real exterior scale. -/
theorem eventually_exterior_volume_lower {ξ : ℝ} (hξ : 0 < 1 - ξ) :
    ∀ᶠ k : ℕ in atTop, ∀ r R : ℕ, 1 ≤ r → 1 ≤ R →
      (k : ℝ) ^ (1 - ξ) / 2 ≤ (exterior ξ r k * R : ℕ) := by
  filter_upwards [eventually_rpow_gap hξ 2] with k hk
  rw [Real.rpow_zero, mul_one] at hk
  have hfloor := Nat.lt_floor_add_one ((k : ℝ) ^ (1 - ξ))
  change _ < (width k (1 - ξ) : ℝ) + 1 at hfloor
  intro r R hr hR
  have hwidth : width k (1 - ξ) ≤ exterior ξ r k * R :=
    (Nat.le_mul_of_pos_left _ hr).trans (Nat.le_mul_of_pos_right _ hR)
  exact le_trans (by linarith only [hk, hfloor] : (k : ℝ) ^ (1 - ξ) / 2 ≤ width k (1 - ξ))
    (by exact_mod_cast hwidth)

/-- The sum of the rounded physical capacities is at most five volume budgets. -/
theorem eventually_padded_charge {α ξ : ℝ} (hα : 0 < α) (a bc : ℕ) (hbc : 0 < bc)
    (hgap : 8 * α * a < 1 - ξ) :
    ∀ᶠ k : ℕ in atTop, ∀ W : ℝ, (k : ℝ) ^ (1 - ξ) / 2 ≤ W →
      let Z := (alphabet α k) ^ a
      ((blocksFor W bc Z * bc * Z ^ 2 : ℕ) : ℝ) ≤ 5 * W := by
  filter_upwards [eventually_labelCount_power hα a 2,
    eventually_rpow_gap hgap (2 * bc), eventually_ge_atTop 1] with k hZ hgapk hk
  intro W hW Z
  have hpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hd : 0 < alphabet α k := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hpos _)
  have hZpos : 0 < Z := pow_pos hd a
  have hWpos : 0 ≤ W := (by positivity : 0 ≤ (k : ℝ) ^ (1 - ξ) / 2).trans hW
  have hZ' : (Z : ℝ) ^ 2 ≤ (k : ℝ) ^ (8 * α * a) := by
    have he : 4 * α * a * (2 : ℕ) = 8 * α * a := by push_cast; ring
    rw [he] at hZ
    exact hZ
  have hround : (bc : ℝ) * Z ^ 2 ≤ W := by
    have h := (mul_le_mul_of_nonneg_left hZ' (by positivity : 0 ≤ 2 * (bc : ℝ))).trans hgapk
    linarith only [h, hW]
  have hp := (pairWidth_bounds hWpos hbc hZpos).2
  rw [pairWidth, Nat.mul_comm bc] at hp
  change ((blocksFor W bc Z * bc : ℕ) : ℝ) * Z ^ 2 < _ at hp
  rw [Nat.cast_mul, Nat.cast_pow]
  linarith only [hp, hround]

/-- Uniform thresholds for the coordinate fraction, single-group load, padded
volume and incoming data of a physical team schedule. -/
theorem eventually_group_charge_room {α ξ : ℝ} (hα : 0 < α) (hξ : ξ < α / 3)
    (a bc M : ℕ) (hbc : 0 < bc) (hgap : 8 * α * a < 1 - ξ) :
    ∀ᶠ k : ℕ in atTop, ∀ r R : ℕ, 1 ≤ r → 1 ≤ R → (R : ℝ) ≤ (k : ℝ) ^ (2 * α) →
      let d := alphabet α k
      let W := exterior ξ r k * R
      (a : ℝ) / d ≤ 1 / 10 ^ 6 ∧ 1024 * (10 * (M + 1) + 4) * R ≤ d ∧
        blocksFor W bc (d ^ a) * bc * (d ^ a) ^ 2 ≤ 5 * W ∧
        ∀ width : ℕ, width ≤ 3 * R * r * literal α k → 4096 * width ≤ W := by
  have hext : 0 < 1 - ξ := lt_of_le_of_lt (by positivity) hgap
  let C : ℕ := 1024 * (10 * (M + 1) + 4)
  filter_upwards [eventually_rpow_gap (show 0 < 3 * α by positivity) (10 ^ 6 * (a : ℝ)),
    eventually_rpow_gap (show 2 * α < 3 * α by linarith) C,
    eventually_padded_charge hα a bc hbc hgap, eventually_exterior_volume_lower hext,
    eventually_literals_le hξ 12288, eventually_ge_atTop 1] with k ha hC hpad hW hdata hk
  intro r R hr hR hRmax d W
  have hceil : (k : ℝ) ^ (3 * α) ≤ d := Nat.le_ceil _
  have hd : 0 < (d : ℝ) := (Real.rpow_pos_of_pos (by exact_mod_cast hk) _).trans_le hceil
  rw [Real.rpow_zero, mul_one] at ha
  refine ⟨(div_le_iff₀ hd).mpr (by linarith only [ha, hceil]), ?_, ?_, ?_⟩
  · have h := (mul_le_mul_of_nonneg_left hRmax (Nat.cast_nonneg C)).trans (hC.trans hceil)
    exact_mod_cast h
  · exact_mod_cast hpad W (hW r R hr hR)
  · intro width hwidth
    calc
      4096 * width ≤ 4096 * (3 * R * r * literal α k) := Nat.mul_le_mul_left _ hwidth
      _ = (12288 * r * literal α k) * R := by ring
      _ ≤ W := Nat.mul_le_mul_right R (hdata r)

end Cube.Physical

end BorderVNP
end Computability
end OAI
