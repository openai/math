import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Density of a padded box

If at most `k` axes each lose at most `H` residues from their common padded
width `X`, the fraction of excluded addresses is at most `k * H / X`.
The residual power-of-two axis can be multiplied into the two volumes exactly.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

/-- Union bound on the fraction of addresses lost by shortening each axis. The
inequality is cross-multiplied, so it holds for natural cardinalities. -/
theorem box_volume_lower (as : List ℕ) (X H : ℕ)
    (hfit : as.length * H ≤ X) (haxis : ∀ a ∈ as, X - H ≤ a) :
    (X - as.length * H) * X ^ as.length ≤ X * as.prod := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.length_cons, Nat.add_mul, one_mul] at hfit ⊢
    have hinner : as.length * H ≤ X := by omega
    have ha := haxis a (by simp)
    have hstep : (X - (as.length * H + H)) * X ≤ (X - as.length * H) * a := by
      calc
        _ ≤ (X - as.length * H) * (X - H) := by
          zify [hfit, hinner, show H ≤ X by omega]
          nlinarith [show 0 ≤ (as.length : ℤ) * (H : ℤ) * (H : ℤ) by positivity]
        _ ≤ _ := Nat.mul_le_mul_left _ ha
    calc
      _ = ((X - (as.length * H + H)) * X) * X ^ as.length := by rw [pow_succ]; ring
      _ ≤ ((X - as.length * H) * a) * X ^ as.length := Nat.mul_le_mul_right _ hstep
      _ = ((X - as.length * H) * X ^ as.length) * a := by ring
      _ ≤ (X * as.prod) * a := Nat.mul_le_mul_right _ (ih hinner (fun b hb => haxis b (by simp [hb])))
      _ = X * (a :: as).prod := by simp; ring

/-- With at most half the padded volume lost, twice the genuine volume
dominates the padded volume. -/
theorem box_half_occupied (as : List ℕ) (X H k : ℕ) (hX : 0 < X)
    (hlen : as.length ≤ k) (hfit : 2 * k * H ≤ X)
    (haxis : ∀ a ∈ as, X - H ≤ a) : X ^ as.length ≤ 2 * as.prod := by
  have hbound : 2 * (as.length * H) ≤ X := by
    rw [Nat.mul_assoc] at hfit
    exact (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right H hlen)).trans hfit
  have h := box_volume_lower as X H (by omega) haxis
  apply Nat.le_of_mul_le_mul_left _ hX
  calc
    _ ≤ (2 * (X - as.length * H)) * X ^ as.length :=
      Nat.mul_le_mul_right _ (by omega)
    _ ≤ 2 * (X * as.prod) := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ h
    _ = X * (2 * as.prod) := by ring

/-- When there are `k / l` full axes and a residual axis of width `k % l`,
the padding volume is exactly `2 ^ k`. -/
theorem box_half_occupied_remainder (as : List ℕ) (k l H : ℕ)
    (hlen : as.length = k / l) (hfit : 2 * k * H ≤ 2 ^ l)
    (haxis : ∀ a ∈ as, 2 ^ l - H ≤ a) :
    2 ^ k ≤ 2 * (as.prod * 2 ^ (k % l)) := by
  have h := box_half_occupied as (2 ^ l) H k (by positivity) (hlen ▸ Nat.div_le_self ..) hfit haxis
  calc
    2 ^ k = (2 ^ l) ^ as.length * 2 ^ (k % l) := by
      rw [hlen, ← pow_mul, ← pow_add, Nat.add_comm, Nat.mod_add_div]
    _ ≤ (2 * as.prod) * 2 ^ (k % l) := Nat.mul_le_mul_right _ h
    _ = _ := Nat.mul_assoc ..

end NearSquareRoot
end Computability
end OAI
