import OAI.Computability.NearSquareRoot.InterchangeSpace

/-!
# A local space allowance for recursive interchange

One unit of width descent pays for the parked descriptor, including on
full-volume calls. Parking an additional array is allowed on a descent
whose physical child volume shrinks by one third.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

def interchangeSpacePotential (A B width volume : ℕ) :=
  3 * A * volume + B * (width + 1) * (Nat.log 2 volume + 1)

/-- Either kind of descent fits the child together with all parent data kept
live during the call. The bound uses the logarithm of this parent volume. -/
theorem interchange_space_potential_descend {A B w f V U park : ℕ}
    (hw : f < w) (hV : U ≤ V)
    (hpark : park ≤ B * (Nat.log 2 V + 1) ∨
      park ≤ A * V + B * (Nat.log 2 V + 1) ∧ 3 * U ≤ 2 * V) :
    park + interchangeSpacePotential A B f U ≤ interchangeSpacePotential A B w V := by
  let n := Nat.log 2 V + 1
  have hr : Nat.log 2 U + 1 ≤ n := Nat.succ_le_succ (Nat.log_mono_right hV)
  have hd : B * n + B * (f + 1) * (Nat.log 2 U + 1) ≤ B * (w + 1) * n := calc
    _ ≤ B * n + B * (f + 1) * n := Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _
    _ = B * (f + 2) * n := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  unfold interchangeSpacePotential
  change park + (3 * A * U + _) ≤ 3 * A * V + B * (w + 1) * n
  rcases hpark with h | ⟨h, shrink⟩
  · change park ≤ B * n at h
    have := Nat.mul_le_mul_left (3 * A) hV
    omega
  · change park ≤ A * V + B * n at h
    have ha : A * V + 3 * A * U ≤ 3 * A * V := calc
      _ = A * V + A * (3 * U) := by ring
      _ ≤ A * V + A * (2 * V) := Nat.add_le_add_left (Nat.mul_le_mul_left _ shrink) _
      _ = _ := by ring
    omega

/-- At every request the allowance is linear in actual tape volume, even
when the number of active bits changes at run time. -/
theorem interchange_space_potential_linear (A B w V : ℕ) (hV : 2 ^ w ≤ V) :
    interchangeSpacePotential A B w V ≤ (3 * A + 4 * B) * V := by
  have hv : V ≠ 0 := Nat.ne_of_gt ((Nat.pow_pos (by decide : 0 < 2)).trans_le hV)
  have hw := (Nat.le_log_iff_pow_le (by decide : 1 < 2) hv).mpr hV
  have hd : B * (w + 1) * (Nat.log 2 V + 1) ≤ 4 * B * V := calc
    _ ≤ B * (Nat.log 2 V + 1) * (Nat.log 2 V + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.succ_le_succ hw))
    _ = B * (Nat.log 2 V + 1) ^ 2 := by ring
    _ ≤ B * (4 * V) := Nat.mul_le_mul_left _ (interchange_log_square_le _ hv)
    _ = _ := by ring
  unfold interchangeSpacePotential
  rw [Nat.add_mul]
  exact Nat.add_le_add_left hd _

end NearSquareRoot
end Computability
end OAI
