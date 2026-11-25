import OAI.ThreeFlat.Diagonal.TraceBucketMasks
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # A fixed word program for the trace receiver's displacement masks -/

namespace Hierarchy.TraceReceiverMaskExpr

open ThreeFlat Diagonal Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.DescriptorExpr
open scoped Fin.CommRing

/-- The input register contains the mask ordinal. A shared zero, one, and
width feed the singleton and low-bit mask calculations and their selectors. -/
def maskTerm (W d : ℕ) : Term W 1 1 :=
  .bind (.literal 0) <|
  .bind (.literal 1) <|
  .bind (.literal d) <|
  .bind (.binary .sub 3 1) <|
  .bind (.binary .shiftLeft 2 0) <|
  .bind (.binary .sub 5 2) <|
  .bind (.binary .shiftLeft 4 0) <|
  .bind (.binary .sub 0 5) <|
  .bind (.select .lt 5 8 0 3) <|
  .bind (.select .eq 9 8 8 0) (.result 0)

@[simp] theorem binds_mask (W d : ℕ) : (maskTerm W d).binds=10 := rfl

private theorem shift_one {W n : ℕ} (nw : n<W) (fit : n<2^W) (one : 1<2^W) :
    BinaryOp.shiftLeft.eval (1 : Word W) (n : Word W) = ((2^n : ℕ) : Word W) := by
  have eqn := PhysicalPinsExpr.op_cast (w:=W) .shiftLeft 1 n ⟨one,fit⟩
  simpa [PhysicalPinsExpr.natOp,nw,Nat.shiftLeft_eq] using eqn

/-- All selected operations have their natural values at each legal ordinal. -/
theorem eval_mask {W d i : ℕ} (dw : d<W) (num : 1+(d+d)<2^W)
    (hi : i<1+(d+d)) (pub : Fin 1→Word W) (m : Memory W) :
    (maskTerm W d).eval pub m (fun _=>(i:Word W))=(TracePhysical.maskNat d i:Word W) := by
  have fi : i<2^W := by omega
  have fd : d<2^W := by omega
  have one : 1<2^W := by omega
  have zero : Comparison.eq.test (i : Word W) 0=decide (i=0) :=
    PhysicalPinsExpr.test_cast .eq i 0 fi (by omega)
  have exceeds : Comparison.lt.test (d : Word W) (i : Word W)=decide (d < i) :=
    PhysicalPinsExpr.test_cast .lt d i fd fi
  change (if Comparison.eq.test (i : Word W) 0 then 0 else
    if Comparison.lt.test (d : Word W) (i : Word W) then
      BinaryOp.sub.eval (BinaryOp.shiftLeft.eval 1 (BinaryOp.sub.eval (i : Word W) d)) 1
    else BinaryOp.shiftLeft.eval 1 (BinaryOp.sub.eval (i : Word W) 1)) = _
  rw [zero,exceeds]
  by_cases iz : i=0
  · simp [iz,TracePhysical.maskNat]
  by_cases small : i≤d
  · have sub : BinaryOp.sub.eval (i : Word W) 1 = ((i-1 : ℕ) : Word W) :=
      PhysicalPinsExpr.op_cast .sub i 1 (show 1 ≤ i by omega)
    simp [iz,small,not_lt.mpr small,TracePhysical.maskNat,sub,shift_one (show i-1<W by omega)
      (show i-1<2^W by omega) one]
  · have gt : d < i := by omega
    have sub : BinaryOp.sub.eval (i : Word W) (d : Word W) = ((i-d : ℕ) : Word W) :=
      PhysicalPinsExpr.op_cast .sub i d gt.le
    have top : BinaryOp.sub.eval ((2^(i-d) : ℕ):Word W) 1 = ((2^(i-d)-1 : ℕ) : Word W) :=
      PhysicalPinsExpr.op_cast .sub (2^(i-d)) 1 (Nat.two_pow_pos (i-d))
    simp [iz,small,gt,TracePhysical.maskNat,sub,shift_one (show i-d<W by omega)
      (show i-d<2^W by omega) one]
    simpa only [Nat.cast_sub (show 1 ≤ 2^(i-d) from Nat.two_pow_pos _),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using top

end Hierarchy.TraceReceiverMaskExpr

end OAI
