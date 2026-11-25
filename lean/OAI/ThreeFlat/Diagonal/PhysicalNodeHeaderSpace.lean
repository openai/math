import OAI.ThreeFlat.Diagonal.PhysicalRegisterSpace
import OAI.ThreeFlat.Diagonal.TickScratchRegion

namespace OAI
/-! # Word and scratch space for the physical node headers -/

namespace ThreeFlat.Diagonal.PhysicalStage

/-- Space for one sixteen-word header per repeated-program stage and the terminal header. -/
theorem Block.directory_header_space {F : Type} [Field F] (B : Block F) {u : ℕ}
    (hu : 40 ≤ u) (levels : B.levels + 1 ≤ u) (rem k : ℕ) :
    16 * (((B.repeat (u^8)).directory rem k).length + 1) ≤ TickWorkspace.stride u := by
  have stages : ((B.repeat (u^8)).directory rem k).length ≤ u^9 := by
    rw [Program.directory_length, program_length, B.repeat_effects_length]
    exact (Nat.mul_le_mul_right (u^8) levels).trans_eq (by ring)
  have pos : 1 ≤ u^9 := Nat.pow_pos (by omega)
  calc
    _ ≤ 32 * u^9 := by omega
    _ ≤ u*u^9 := Nat.mul_le_mul_right _ (by omega)
    _ = u^10 := by ring
    _ ≤ 2^(u^10) := Nat.lt_two_pow_self.le
    _ ≤ TickWorkspace.stride u := Nat.le_self_pow (by decide : 4 ≠ 0) _

theorem node_word_space {u : ℕ} (hu : 40 ≤ u) :
    16 < 2^(16*u^10) ∧ 44 < TickWorkspace.stride u := by
  have age : u ≤ u^10 := Nat.le_self_pow (by decide) _
  have radix : 64 ≤ 2^(u^10) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ u^10)
  have width : 64 ≤ 2^(16*u^10) :=
    radix.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have stride : 64 ≤ TickWorkspace.stride u :=
    radix.trans (Nat.le_self_pow (by decide : 4 ≠ 0) _)
  omega

/-- Eight words per initial node fit in the region for the seed rows. -/
theorem seed_rows_space {u k : ℕ} (hu : 40 ≤ u) (depth : k ≤ u^10+2*u^6) :
    8*(k*2^k) ≤ TickWorkspace.stride u := by
  have power : u ≤ u^4 := Nat.le_self_pow (by decide) _
  have gap : 16*u^6 ≤ u^10 := by
    calc
      _ ≤ u^4*u^6 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have pos : 1 ≤ u^6 := Nat.pow_pos (by omega)
  calc
    _ ≤ 2^3*(2^k*2^k) := Nat.mul_le_mul_left 8 (Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le)
    _ = 2^(3+(k+k)) := by rw [pow_add, pow_add]
    _ ≤ 2^(u^10*4) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = TickWorkspace.stride u := pow_mul ..

end ThreeFlat.Diagonal.PhysicalStage

end OAI
