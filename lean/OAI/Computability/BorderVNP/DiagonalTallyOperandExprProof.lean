import OAI.Computability.BorderVNP.DiagonalTallyOperandExpressions

/-! # Arithmetic correctness and word bounds for compact tally descriptors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyOperandArray

open RoutingISA

variable (f : Frame) (k : Kind) {w : ℕ} (fit : f.Fits k w)
include fit

/-- Every expression for a reference uses a positive divisor exactly when it is executed. -/
theorem refExpr_correct (pub : Arg → ℕ) (z : NatState) (i : ℕ) (h : i<f.nrefs k)
    (load : f.Loaded z.reg) (idx : z.reg 40=i) (unit : z.reg 43=1) :
    (refExpr k).safeReadOnly w pub z.mem z.reg ∧
      (refExpr k).evalNat pub z.mem z.reg 50=f.refValue k i := by
  have hend := fit.externalEnd
  obtain ⟨_,_,width,_,_,_,ext,_,_,_⟩ := load
  cases k with
  | unary =>
    simp [refExpr,Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,Frame.refValue,ext,idx]
    omega
  | count =>
    change i<f.gadgets*f.width at h
    change f.external+f.gadgets*f.width<2^w at hend
    have hp : 0<f.width := by
      by_contra! hz
      have e : f.width=0 := by omega
      simp [e] at h
    have modlt := Nat.mod_lt i hp
    have modle := Nat.mod_le i f.width
    have divlt := (Nat.div_lt_iff_lt_mul hp).mpr h
    have prod := Nat.mul_le_mul_right f.width (Nat.succ_le_of_lt divlt)
    rw [Nat.succ_mul] at prod
    have split := Nat.div_add_mod' i f.width
    simp [refExpr,Code.block,Code.safeReadOnly,Code.evalNat,Function.update,addressOpFits,addressOp,
      idx,unit,width,ext,Frame.refValue]
    omega

/-- The physical row contains exactly the five fields expected by the operand
materializer, including the last cursor, on all marked copies and all gadgets. -/
theorem fieldExpr_correct (pub : Arg → ℕ) (z : NatState) (i : ℕ) (h : i<5*f.nrows k)
    (load : f.Loaded z.reg) (idx : z.reg 40=i) (unit : z.reg 43=1) :
    (fieldExpr k).safeReadOnly w pub z.mem z.reg ∧
      (fieldExpr k).evalNat pub z.mem z.reg 50=f.field k i := by
  obtain ⟨par,_,width,zeroAddr,side,copies,_,_,refs,_⟩ := load
  have hsmall := fit.small
  have sBound := fit.sideEnd
  have rBound := fit.refsEnd
  have cBound := fit.coordinateEnd
  have row : i/5<f.nrows k := by omega
  cases k with
  | unary =>
    change i/5<f.marked*f.copies at row
    change f.refs+f.marked*f.copies<2^w at rBound
    have hp : 0<f.copies := by
      by_contra! hz
      have e : f.copies=0 := by omega
      simp [e] at row
    have source : i/5/f.copies<f.marked := (Nat.div_lt_iff_lt_mul hp).mpr row
    by_cases c0 : i%5=0 <;> by_cases c1 : i%5=1 <;> by_cases c2 : i%5=2 <;> by_cases c3 : i%5=3 <;>
      simp [fieldExpr,Frame.field,Code.block,Code.safeReadOnly,Code.evalNat,Function.update,addressOpFits,addressOp,
        idx,unit,copies,side,refs,c0,c1,c2,c3] <;> omega
  | count =>
    change i/5<f.gadgets at row
    change f.refs+f.gadgets*f.width<2^w at rBound
    have prod := Nat.mul_le_mul_right f.width (Nat.succ_le_of_lt row)
    rw [Nat.succ_mul] at prod
    by_cases c0 : i%5=0 <;> by_cases c1 : i%5=1 <;> by_cases c2 : i%5=2 <;> by_cases c3 : i%5=3 <;>
      simp [fieldExpr,Frame.field,Code.block,Code.safeReadOnly,Code.evalNat,Function.update,addressOpFits,addressOp,
        idx,unit,width,zeroAddr,par,refs,c0,c1,c2,c3] <;> omega

end DiagonalTallyOperandArray

end BorderVNP
end Computability
end OAI
