import OAI.Computability.QuantumFactoring.BitArithmeticDivision
import OAI.ThreeFlat.Diagonal.TraceWordTests

namespace OAI
/-! # Arithmetic circuits for two register operands -/

namespace ThreeFlat.Diagonal.TraceArithmeticOps

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM ExactQuantumFactoring TraceWords

variable {w : ℕ}

/-- Concatenate the two register words in the input order used by the native bitblaster. -/
def inputs (x y : Word w) : Fin (w+w) → Bool := Fin.append (bits x) (bits y)

theorem leftWord_inputs (x y : Word w) :
    BitArithmetic.leftWord (inputs x y) = BitVec.ofFin x := by
  unfold BitArithmetic.leftWord inputs
  simp only [Fin.append_left]
  exact bitsValue_bits (BitVec.ofFin x)

theorem rightWord_inputs (x y : Word w) :
    BitArithmetic.rightWord (inputs x y) = BitVec.ofFin y := by
  unfold BitArithmetic.rightWord inputs
  simp only [Fin.append_right]
  exact bitsValue_bits (BitVec.ofFin y)

theorem add_correct (x y : Word w) (j : Fin w) :
    (BitArithmetic.add w).eval (inputs x y) j = bits (BinaryOp.add.eval x y) j := by
  rw [BitArithmetic.add_correct, leftWord_inputs, rightWord_inputs]
  rfl

theorem sub_correct (x y : Word w) (j : Fin w) :
    (BitArithmetic.sub w).eval (inputs x y) j = bits (BinaryOp.sub.eval x y) j := by
  rw [BitArithmetic.sub_correct, leftWord_inputs, rightWord_inputs]
  rfl

theorem mul_correct (x y : Word w) (j : Fin w) :
    (BitArithmetic.mul w).eval (inputs x y) j = bits (BinaryOp.mul.eval x y) j := by
  rw [BitArithmetic.mul_correct, leftWord_inputs, rightWord_inputs]
  rfl

/-- A zero register divisor gives a zero quotient, including at width zero. -/
theorem div_correct (x y : Word w) (j : Fin w) :
    (BitArithmetic.div w).eval (inputs x y) j = bits (BinaryOp.div.eval x y) j := by
  rw [BitArithmetic.div_correct, leftWord_inputs, rightWord_inputs]
  simp only [BitVec.getLsbD, BitVec.toNat_udiv, BitVec.toNat_ofFin, bits, BinaryOp.eval,
    Fin.val_ofNat, Nat.mod_eq_of_lt ((Nat.div_le_self x.val y.val).trans_lt x.isLt)]

/-- A zero register divisor returns the dividend as remainder. -/
theorem mod_correct (x y : Word w) (j : Fin w) :
    (BitArithmetic.mod w).eval (inputs x y) j = bits (BinaryOp.mod.eval x y) j := by
  rw [BitArithmetic.mod_correct, leftWord_inputs, rightWord_inputs]
  simp only [BitVec.getLsbD, BitVec.toNat_umod, BitVec.toNat_ofFin, bits, BinaryOp.eval,
    Fin.val_ofNat, Nat.mod_eq_of_lt ((Nat.mod_le x.val y.val).trans_lt x.isLt)]

end ThreeFlat.Diagonal.TraceArithmeticOps

end OAI
