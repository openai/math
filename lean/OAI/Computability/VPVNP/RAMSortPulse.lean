import Mathlib.Data.Nat.Basic

/-!
# Boolean bitonic sequences

A cyclic block of consecutive ones describes the thresholded input to a
bitonic merge. Comparing opposite positions splits the block into two
shorter blocks, independently of its starting position.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

/-- A periodic sequence whose first `ones` positions after shifting are true. -/
def pulse (width shift ones i : ℕ) : Bool := decide ((i + shift) % width < ones)

private theorem opposite_residues (x : ℕ) {n : ℕ} (hn : 0 < n) :
    (x % (2 * n) = x % n ∧ (x + n) % (2 * n) = x % n + n) ∨
    (x % (2 * n) = x % n + n ∧ (x + n) % (2 * n) = x % n) := by
  let r := x % (2 * n)
  have hr : r < 2 * n := Nat.mod_lt _ (by omega)
  have hsmall : r % n = x % n := Nat.mod_mod_of_dvd _ ⟨2, Nat.mul_comm ..⟩
  have hopp : (r + n) % (2 * n) = (x + n) % (2 * n) := Nat.mod_add_mod ..
  change (r = _ ∧ _) ∨ (r = _ ∧ _)
  rw [← hsmall, ← hopp]
  by_cases h : r < n
  · left
    rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show r + n < 2 * n by omega)]
    exact ⟨rfl, rfl⟩
  · right
    have h₁ : r % n = r - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have h₂ : (r + n) % (2 * n) = r - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [h₁, h₂]
    omega

/-- The smaller Boolean output at each opposite pair is a pulse with the
excess over half the original width. -/
theorem pulse_and {n : ℕ} (hn : 0 < n) (shift ones i : ℕ) :
    (pulse (2 * n) shift ones i && pulse (2 * n) shift ones (i + n)) =
      pulse n shift (ones - n) i := by
  simp only [pulse, ← Bool.decide_and, decide_eq_decide]
  rw [show i + n + shift = i + shift + n by omega]
  rcases opposite_residues (i + shift) hn with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    rw [h₁, h₂] <;> omega

/-- The larger Boolean output at each opposite pair is a pulse capped at
half the original width. -/
theorem pulse_or {n : ℕ} (hn : 0 < n) (shift ones i : ℕ) :
    (pulse (2 * n) shift ones i || pulse (2 * n) shift ones (i + n)) =
      pulse n shift (min ones n) i := by
  simp only [pulse, ← Bool.decide_or, decide_eq_decide]
  rw [show i + n + shift = i + shift + n by omega]
  have hlt := Nat.mod_lt (i + shift) hn
  rcases opposite_residues (i + shift) hn with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    rw [h₁, h₂] <;> omega

/-- A rising segment at cut `a` followed by a falling segment at cut `b`
forms one cyclic pulse of length `n - a + b`. -/
theorem pulse_of_segments {n a b i : ℕ} (ha : a ≤ n) (hb : b ≤ n) (hi : i < 2 * n) :
    pulse (2 * n) (2 * n - a) (n - a + b) i =
      if i < n then decide (a ≤ i) else decide (i - n < b) := by
  unfold pulse
  by_cases h : i < a
  · rw [ite_eq_left (show i < n by omega), Nat.mod_eq_of_lt (by omega), decide_eq_decide]
    omega
  · have hm : (i + (2 * n - a)) % (2 * n) = i - a := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hm]
    split <;> rw [decide_eq_decide] <;> omega

end RAMSort

end VPVNP
end Computability
end OAI
