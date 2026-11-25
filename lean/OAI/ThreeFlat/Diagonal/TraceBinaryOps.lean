import OAI.ThreeFlat.Diagonal.TraceArithmeticOps
import OAI.ThreeFlat.Diagonal.TraceBitwiseOps

namespace OAI
/-! # A polynomial-size Boolean network for every binary RAM opcode -/

namespace ThreeFlat.Diagonal.TraceBinaryOps

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM ExactQuantumFactoring

/-- Compile a RAM opcode at a public width. The two input words are in little-endian order. -/
def network (op : BinaryOp) (w : ℕ) : BooleanNetwork (w+w) w :=
  match op with
  | .add => BitArithmetic.add w
  | .sub => BitArithmetic.sub w
  | .mul => BitArithmetic.mul w
  | .div => BitArithmetic.div w
  | .mod => BitArithmetic.mod w
  | .bitAnd => TraceBitwiseOps.network .bitAnd w
  | .bitOr => TraceBitwiseOps.network .bitOr w
  | .bitXor => TraceBitwiseOps.network .bitXor w
  | .shiftLeft => TraceBitwiseOps.network .shiftLeft w
  | .shiftRight => TraceBitwiseOps.network .shiftRight w

theorem network_correct {w : ℕ} (op : BinaryOp) (x y : Word w) (j : Fin w) :
    (network op w).eval (Fin.append (TraceWords.bits x) (TraceWords.bits y)) j =
      TraceWords.bits (op.eval x y) j := by
  cases op with
  | add => exact TraceArithmeticOps.add_correct x y j
  | sub => exact TraceArithmeticOps.sub_correct x y j
  | mul => exact TraceArithmeticOps.mul_correct x y j
  | div => exact TraceArithmeticOps.div_correct x y j
  | mod => exact TraceArithmeticOps.mod_correct x y j
  | bitAnd => exact TraceBitwiseOps.network_correct .bitAnd x y j
  | bitOr => exact TraceBitwiseOps.network_correct .bitOr x y j
  | bitXor => exact TraceBitwiseOps.network_correct .bitXor x y j
  | shiftLeft => exact TraceBitwiseOps.network_correct .shiftLeft x y j
  | shiftRight => exact TraceBitwiseOps.network_correct .shiftRight x y j

/-- The single cubic bound covers every opcode, including at width zero. -/
theorem network_count (op : BinaryOp) (w : ℕ) :
    (network op w).net.count ≤ 216*(w+1)^3 := by
  have bitwise (b : TraceBitwiseOps.Op) : (TraceBitwiseOps.network b w).net.count ≤ 216*(w+1)^3 :=
    (TraceBitwiseOps.network_count b w).trans (Nat.mul_le_mul_right _ (by decide))
  cases op with
  | add => exact (BitArithmetic.add_count w).trans (by ring_nf; omega)
  | sub => exact (BitArithmetic.sub_count w).trans (by ring_nf; omega)
  | mul => exact (BitArithmetic.mul_count w).trans (by ring_nf; omega)
  | div => exact (BitArithmetic.div_count w).trans (by ring_nf; omega)
  | mod => exact (BitArithmetic.mod_count w).trans (by ring_nf; omega)
  | bitAnd => exact bitwise .bitAnd
  | bitOr => exact bitwise .bitOr
  | bitXor => exact bitwise .bitXor
  | shiftLeft => exact bitwise .shiftLeft
  | shiftRight => exact bitwise .shiftRight

end ThreeFlat.Diagonal.TraceBinaryOps

end OAI
