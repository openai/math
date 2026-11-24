import OAI.Computability.VPVNP.TensorPowerIncidence
import OAI.Computability.VPVNP.IncidenceReindex
import OAI.Computability.VPVNP.IncidenceProjection
import Mathlib.Tactic.Ring

/-! # Tensor powers as projections with a near-linear input length

The exact-one table has one row per party, position and digit comparison.
Its row count is linear in the power index. The columns are the one-hot
flags, whose count grows at the rate of the local dimension to that power.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TensorPowerCNF
open scoped Classical

private def rowCoefficient (b d : ℕ) := d + d * b + 2

/-- Uniform constant in the source-length estimate for the exact-one table. -/
def sharpCoefficient (b d : ℕ) :=
  1000000 * rowCoefficient b d ^ 4 + (d + (2 ^ b) ^ d) * rowCoefficient b d + 1

private theorem table_size_le (J : Type*) [Fintype J] (b h : ℕ) :
    1000000 * (Fintype.card (Row J b h) + 1) ^ 4 +
      Fintype.card (Col J b h) * (Fintype.card (Row J b h) + 2) + 1 ≤
      sharpCoefficient b (Fintype.card J) * (h + 1) ^ 4 * (2 ^ b) ^ h := by
  let d := Fintype.card J
  let u := (2 ^ b) ^ h
  let M := rowCoefficient b d
  let K := d + (2 ^ b) ^ d
  have hu : 0 < u := by
    dsimp [u]
    positivity
  have hm : Fintype.card (Row J b h) + 2 ≤ M * (h + 1) := by
    rw [card_row]
    dsimp [M, rowCoefficient, d]
    nlinarith only [Nat.zero_le (Fintype.card J * h), Nat.zero_le (Fintype.card J * b)]
  have hk : Fintype.card (Col J b h) ≤ K * (h + 1) * u := by
    rw [card_col]
    change d * u + h * (2 ^ b) ^ d ≤ _
    calc
      _ ≤ d * ((h + 1) * u) + (2 ^ b) ^ d * ((h + 1) * u) := by
        apply Nat.add_le_add
        · apply Nat.mul_le_mul_left
          exact Nat.le_mul_of_pos_left _ (by omega)
        · rw [Nat.mul_comm h]
          exact Nat.mul_le_mul_left _ ((Nat.le_succ h).trans (Nat.le_mul_of_pos_right _ hu))
      _ = _ := by
        dsimp [K]
        ring
  have hp : (h + 1) ^ 2 ≤ (h + 1) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hprefix : 1000000 * (Fintype.card (Row J b h) + 1) ^ 4 ≤
      (1000000 * M ^ 4) * (h + 1) ^ 4 * u := by
    refine (Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_left (le_trans ?_ hm) 4)).trans ?_
    · omega
    · rw [mul_pow, ← mul_assoc]
      exact Nat.le_mul_of_pos_right _ hu
  have hpayload : Fintype.card (Col J b h) * (Fintype.card (Row J b h) + 2) ≤
      (K * M) * (h + 1) ^ 4 * u := by
    calc
      _ ≤ (K * (h + 1) * u) * (M * (h + 1)) := Nat.mul_le_mul hk hm
      _ = (K * M) * (h + 1) ^ 2 * u := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)
  have hunit : 1 ≤ (h + 1) ^ 4 * u := Nat.mul_pos (Nat.pow_pos (by omega)) hu
  refine (Nat.add_le_add (Nat.add_le_add hprefix hpayload) hunit).trans_eq ?_
  dsimp [sharpCoefficient, M, K, d, u]
  ring

variable {J R : Type*} [Fintype J] [CommRing R] {b : ℕ}

/-- At every length above this explicit bound, the universal polynomial projects
to the tensor power. The bound depends only on the bit width and party count. -/
theorem projection_at_sharp_length (T : (J → Digit b) → R) (h n : ℕ)
    (hn : sharpCoefficient b (Fintype.card J) * (h + 1) ^ 4 * (2 ^ b) ^ h ≤ n) :
    ∃ φ : Projection R (Fin n × Bool) (J × Word b h),
      φ.hom (MvPolynomial.map (Int.castRingHom R) (P n)) = form T h := by
  let rows := (Fintype.equivFin (Row J b h)).symm
  let cols := (Fintype.equivFin (Col J b h)).symm
  obtain ⟨φ, hφ⟩ := IncidenceMachine.weighted_projection
    (fun r i => incidence (rows r) (cols i)) (columnWeight T h ∘ cols) n
    ((table_size_le J b h).trans hn)
  refine ⟨φ, hφ.trans ?_⟩
  apply (IncidenceMachine.weighted_exactOne_reindex rows cols incidence (columnWeight T h)).trans
  convert weightedIncidence_eq_form T h using 1
  congr
  exact Subsingleton.elim _ _

/-- The exponential growth rate of the projection length is at most the local
dimension, with polynomial overhead in the power index. -/
theorem sharp_projection (T : (J → Digit b) → R) :
    ∃ A > 0, ∀ h n, A * (h + 1) ^ 4 * (2 ^ b) ^ h ≤ n →
      ∃ φ : Projection R (Fin n × Bool) (J × Word b h),
        φ.hom (MvPolynomial.map (Int.castRingHom R) (P n)) = form T h :=
  ⟨sharpCoefficient b (Fintype.card J), Nat.zero_lt_succ _, projection_at_sharp_length T⟩

end TensorPowerCNF

end VPVNP
end Computability
end OAI
