import OAI.Computability.VPVNP.PrimedInputRAMOpcodeFields

/-!
# Word operations for cursor route geometry

The shift amount is a cursor coordinate below the host word width. The
mask and lane indices fit in one host word. Under these bounds the native
instructions compute the natural-number masks and the Boolean side flags.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteWord

open BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {W i m x y : ℕ}

theorem shl_one (hi : i < W) :
    BinaryOp.shiftLeft.eval (1 : Word W) (i : Word W) = ((2 ^ i : ℕ) : Word W) := by
  have hw : 0 < W := (Nat.zero_le i).trans_lt hi
  simp [BinaryOp.eval, Fin.val_natCast, Nat.mod_eq_of_lt (hi.trans Nat.lt_two_pow_self),
    Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne'), hi, Nat.shiftLeft_eq]

theorem maskBit (hi : i < W) (hm : m < 2 ^ W) :
    BinaryOp.bitAnd.eval (BinaryOp.shiftRight.eval (m : Word W) (i : Word W)) 1 =
      ((m.testBit i).toNat : Word W) := by
  rw [PrimedInputRAM.Opcodes.readBit_word ((Nat.zero_le i).trans_lt hi), Fin.val_natCast,
    Fin.val_natCast, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (hi.trans Nat.lt_two_pow_self)]
  cases m.testBit i <;> rfl

theorem xor_cast (hx : x < 2 ^ W) (hy : y < 2 ^ W) :
    BinaryOp.bitXor.eval (x : Word W) (y : Word W) = ((x ^^^ y : ℕ) : Word W) := by
  change Fin.ofNat _ ((x % (2^W)) ^^^ (y % (2^W))) = _
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  rfl

theorem div_self (hx : x < 2 ^ W) :
    BinaryOp.div.eval (x : Word W) (x : Word W) = (if x = 0 then 0 else 1) := by
  change Fin.ofNat _ ((x % (2^W)) / (x % (2^W))) = _
  rw [Nat.mod_eq_of_lt hx]
  by_cases h : x = 0
  · subst x
    rfl
  · rw [ite_eq_right h, Nat.div_self (Nat.pos_of_ne_zero h)]
    rfl

theorem or_flags (a b : Bool) (hw : 0 < W) :
    BinaryOp.bitOr.eval (a.toNat : Word W) (b.toNat : Word W) = ((a || b).toNat : Word W) := by
  cases a <;> cases b <;> simp [BinaryOp.eval, Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')]

theorem sub_cast (h : y ≤ x) :
    BinaryOp.sub.eval (x : Word W) (y : Word W) = ((x - y : ℕ) : Word W) := by
  exact (Nat.cast_sub h).symm

end PairSimulation.RouteWord

end VPVNP
end Computability
end OAI
