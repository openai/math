import OAI.Computability.VPVNP.CursorRouting
import OAI.Computability.VPVNP.RAMProgram

/-!
# Low-bit masks in the native successor selector

The XOR of a nonwrapping sender and its successor is a nonempty prefix of
one bits. A one-bit right shift shortens that prefix by one. These identities
justify both the selector's initial register and its subsequent countdown.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSuccessorClass

open BurstRAM BurstRAM.PrivateRAM

/-- The bits from zero through `t`, inclusive. -/
def mask (t : ℕ) := 2 ^ (t+1) - 1

theorem mask_one : mask 0 = 1 := rfl

theorem mask_pos (t : ℕ) : 0 < mask t := by
  have h := Nat.two_pow_pos t
  rw [mask, pow_succ]
  omega

theorem one_lt_mask_succ (t : ℕ) : 1 < mask (t+1) := by
  have h := mask_pos t
  rw [mask] at h
  rw [mask, pow_succ _ (t+1)]
  omega

theorem mask_half (t : ℕ) : mask (t+1) / 2 = mask t := by
  have h := Nat.two_pow_pos (t+1)
  rw [mask, mask, pow_succ _ (t+1)]
  omega

theorem mask_lt_mod {t W : ℕ} (h : t < W) : mask t < 2^W := by
  have hle := Nat.pow_le_pow_right (by decide : 0 < 2) (show t+1 ≤ W from h)
  have hp := Nat.two_pow_pos (t+1)
  unfold mask
  omega

theorem step_shift {t W : ℕ} (h : t+1 < W) (a : Word W) (ha : a.val = mask (t+1))
    (one : Word W) (ho : one.val = 1) :
    (BinaryOp.shiftRight.eval a one).val = mask t := by
  simp only [BinaryOp.eval, ho, show 1 < W by omega, ↓reduceIte, Fin.val_ofNat, ha,
    Nat.shiftRight_eq_div_pow, pow_one, mask_half, Nat.mod_eq_of_lt (mask_lt_mod (by omega : t < W))]

/-- The arithmetic instructions produce the mask for the sender's unique
nonwrapping successor class. -/
theorem sender_xor {W : ℕ} (a one : Word W) {D : ℕ} (hD : D ≤ W)
    (hx : a.val+1 < 2^D) (ho : one.val = 1) :
    (BinaryOp.bitXor.eval a (BinaryOp.add.eval a one)).val = mask (CursorRouting.successorClass hx).val := by
  have hnext := hx.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hD)
  have hxor := (CursorRouting.successorClass_eq_iff hx (CursorRouting.successorClass hx)).mp rfl
  change a.val ^^^ (a.val+1) = mask (CursorRouting.successorClass hx).val at hxor
  simp only [BinaryOp.eval, Fin.val_ofNat, Fin.val_add, ho, Nat.mod_eq_of_lt hnext, hxor,
    Nat.mod_eq_of_lt (mask_lt_mod ((CursorRouting.successorClass hx).isLt.trans_le hD))]

end PairSimulation.LeafSuccessorClass

end VPVNP
end Computability
end OAI
