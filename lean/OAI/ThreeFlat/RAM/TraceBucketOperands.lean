import OAI.ThreeFlat.RAM.TraceBucketProjection

namespace OAI
/-! # Exact values of the scalar operands reused in initial bucket records -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open Diagonal.TraceSourceOwner
open scoped Fin.CommRing

variable {W n : ℕ}

theorem laneBase_value (s : Layout) (v : Fin 4 → Word W) (data : Fin 1→Word W) (m : Memory W) :
    (laneBase s).eval data m v = ((v 2).val*s.lowRows : ℕ) := by
  simp [laneBase,Term.eval,BinaryOp.eval]

theorem pinStart_value (s : Layout) (v : Fin 4 → Word W) (data : Fin 1→Word W) (m : Memory W) :
    (pinStart s).eval data m v=(s.pinLow (v 2).val : Word W) := by
  simp only [pinStart,Term.eval_binary,Term.eval_literal,laneBase_value,Layout.pinLow]
  simp [BinaryOp.eval]

theorem ext_value (s : Layout) (v : Fin 4 → Word W) (data : Fin 1→Word W) (m : Memory W)
    (header : s.shape.header<2^W) (extent : s.pinLow (v 2).val+2*s.lowRows<2^W) :
    (ext s).eval data m v = (s.pinCount (v 2).val : Word W) := by
  let x := s.pinLow (v 2).val
  have small : x<2^W := by dsimp [x]; omega
  have len : 2*s.lowRows<2^W := by omega
  simp only [ext,Term.eval_select,Term.eval_literal,Term.eval_binary,pinStart_value]
  change (if Comparison.lt.test (s.shape.header : Word W) (x : Word W) then _ else _) = _
  have bound := PhysicalPinsExpr.test_cast (w:=W) .lt _ _ header small
  rw [bound]
  change (if decide (s.shape.header<x) then _ else _) = _
  by_cases h : s.shape.header<x
  · simp [h,Layout.pinCount,x,Nat.sub_eq_zero_of_le h.le]
  · have le : x≤ s.shape.header := by omega
    have add : BinaryOp.add.eval (x : Word W) (2*s.lowRows : ℕ) =
      (x+2*s.lowRows : ℕ) := by simp [BinaryOp.eval]
    simp only [h,decide_false,Bool.false_eq_true,ite_false]
    change (if Comparison.lt.test (s.shape.header : Word W) (BinaryOp.add.eval (x : Word W)
        ((2*s.lowRows : ℕ) : Word W)) then BinaryOp.sub.eval (s.shape.header : Word W) (x : Word W)
      else ((2*s.lowRows : ℕ) : Word W))=_
    rw [add,PhysicalPinsExpr.test_cast (w:=W) .lt _ _ header (show x+2*s.lowRows<2^W from extent)]
    have sub := PhysicalPinsExpr.op_cast (w:=W) .sub s.shape.header x le
    change (if decide (s.shape.header < x+2*s.lowRows) then
      BinaryOp.sub.eval (s.shape.header : Word W) (x : Word W) else ((2*s.lowRows : ℕ) : Word W)) =
      ((min (s.shape.header-x) (2*s.lowRows) : ℕ) : Word W)
    by_cases full : s.shape.header < x+2*s.lowRows
    · have short : s.shape.header-x≤2*s.lowRows := by omega
      simp [full,sub,natOp,Nat.min_eq_left short]
    · have long : 2*s.lowRows≤ s.shape.header-x := by omega
      simp [full,Nat.min_eq_right long]

theorem raw_value (s : Layout) (v : Fin 4→Word W) (data : Fin 1→Word W) (m : Memory W)
    (site slot leg : Term W 1 4) (i j k : ℕ)
    (hi : site.eval data m v=(i : Word W)) (hj : slot.eval data m v=(j : Word W))
    (hk : leg.eval data m v=(k : Word W)) (fits : s.readAt i j k<2^W) :
    (raw s site slot leg).eval data m v=m (s.readAt i j k) := by
  simp only [raw,Term.eval_load,Term.eval_binary,Term.eval_literal,hi,hj,hk]
  have eqn : (BinaryOp.add.eval (BinaryOp.add.eval (s.records : Word W)
      (BinaryOp.mul.eval ((11 : ℕ) : Word W) (BinaryOp.add.eval (BinaryOp.mul.eval (i : Word W) (s.slots : Word W)) (j : Word W))))
      (k : Word W))=(s.readAt i j k : Word W) := by simp [Layout.readAt,BinaryOp.eval]
  rw [eqn,Fin.val_cast_of_lt fits]

/-- Owner and slot classification are read-free polynomial formulas in the
public dimensions. The arguments are unrelated to the parameter and memory
of the surrounding trace materializer. -/
theorem direct_owner (s : Layout) (data : Fin 1→Word W) (m : Memory W) (v : Fin 4→Word W)
    (x y : Term W 1 4) (a b cap : ℕ) (hx : x.eval data m v=(a : Word W))
    (hy : y.eval data m v=(b : Word W))
    (small : ∀ i, TraceOwnerFormula.vars s.shape 1 a b i<2^cap) (margin : 5*cap+128≤W) :
    (TraceOwnerFormula.direct .owner s.shape 1 x y).eval data m v=(ownerAt s.shape 1 b a : Word W) := by
  rw [TraceOwnerFormula.direct_eval _ _ _ _ _ _ _ _ _ _ hx hy small margin,
    TraceOwnerFormula.owner_natural_at]

end ThreeFlat.RAM.TraceBucketAtom

end OAI
