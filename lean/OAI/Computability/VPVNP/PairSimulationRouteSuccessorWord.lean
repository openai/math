import OAI.Computability.VPVNP.PairSimulationRouteWord
import OAI.Computability.VPVNP.CursorRouting

/-!
# Computing the successor mask and the inactive-send flag

A successor class uses the mask of its lowest `j + 1` bits. The zero-cursor
send is inactive when the site has no nonwrapping successor or its successor
changes a different set of bits. Native xor and self-division test the two
conditions on host words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteWord

open BurstRAM PrivateRAM CursorRouting
open scoped Fin.CommRing

private theorem xor_flag {W a b : ℕ} (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    let t := BinaryOp.bitXor.eval (a : Word W) (b : Word W)
    BinaryOp.div.eval t t = ((decide (a ≠ b)).toNat : Word W) := by
  dsimp only
  rw [xor_cast ha hb, div_self (Nat.xor_lt_two_pow ha hb)]
  by_cases h : a = b <;> simp [h]

/-- The native mask word and rejection flag of a successor system at cursor zero. -/
theorem successor_values {D W : ℕ} (x : Site D) (j : Fin D) (hw : D < W) :
    let shl := fun t : Word W => BinaryOp.shiftLeft.eval 1 t
    let nz := fun t : Word W => BinaryOp.div.eval t t
    let xor := fun a b : Word W => BinaryOp.bitXor.eval a b
    let m := shl (j.val : Word W) + shl (j.val : Word W) - 1
    m = ((systemMask (.inl j)).val : Word W) ∧
      BinaryOp.bitOr.eval (nz (xor (xor (x.val : Word W) ((x.val : Word W) + 1)) m))
        (1 - nz (xor (shl (D : Word W) - 1) (x.val : Word W))) =
        ((decide (¬ (x.val + 1 < 2 ^ D ∧ x.val ^^^ (x.val + 1) = (systemMask (.inl j)).val))).toNat :
          Word W) := by
  dsimp only
  have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) hw
  have hx : x.val < 2^W := x.isLt.trans hp
  have hnext : x.val + 1 < 2^W := (Nat.succ_le_of_lt x.isLt).trans_lt hp
  have hmask : (systemMask (.inl j)).val < 2^W := (systemMask (.inl j)).isLt.trans hp
  have hlast : 2^D - 1 < 2^W := (Nat.sub_le ..).trans_lt hp
  have castMask : ((2 ^ j.val : ℕ) : Word W) + ((2 ^ j.val : ℕ) : Word W) - 1 =
      ((systemMask (.inl j)).val : Word W) := by
    change _ = ((2 ^ (j.val + 1) - 1 : ℕ) : Word W)
    rw [Nat.cast_sub (Nat.two_pow_pos _), Nat.pow_succ, Nat.mul_two, Nat.cast_add, Nat.cast_one]
  have castLast : ((2^D : ℕ) : Word W) - 1 = ((2^D - 1 : ℕ) : Word W) := by
    rw [Nat.cast_sub (Nat.two_pow_pos _), Nat.cast_one]
  have castNext : (x.val : Word W) + 1 = ((x.val + 1 : ℕ) : Word W) := by simp
  rw [shl_one (j.isLt.trans hw), castMask, shl_one hw, castLast, castNext,
    xor_cast hx hnext, xor_flag (Nat.xor_lt_two_pow hx hnext) hmask, xor_flag hlast hx]
  refine ⟨rfl, ?_⟩
  have bound := x.isLt
  have lastFlag : (1 : Word W) - ((decide (2^D - 1 ≠ x.val)).toNat : Word W) =
      ((decide (¬ x.val + 1 < 2^D)).toNat : Word W) := by
    by_cases h : x.val + 1 < 2^D
    · have hne : 2^D - 1 ≠ x.val := by omega
      simp [h, hne]
    · have he : 2^D - 1 = x.val := by omega
      simp [h, he]
  rw [lastFlag, or_flags _ _ ((Nat.zero_le D).trans_lt hw)]
  by_cases h : x.val + 1 < 2^D <;> simp [h]

end PairSimulation.RouteWord

end VPVNP
end Computability
end OAI
