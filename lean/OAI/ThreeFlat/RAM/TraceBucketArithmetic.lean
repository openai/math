import OAI.ThreeFlat.RAM.TraceBucketOperands

namespace OAI
/-! # Compositional natural-number evaluation of scalar address arithmetic -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open scoped Fin.CommRing
variable {W n : ℕ} (data : Fin 1→Word W) (m : Memory W) (v : Fin n→Word W)

theorem binary_value (op : BinaryOp) {a b : Term W 1 n} {x y : ℕ}
    (ha : a.eval data m v=(x : Word W)) (hb : b.eval data m v=(y : Word W)) (fit : opFits W op x y) :
    (Term.binary op a b).eval data m v=(natOp W op x y : Word W) := by
  rw [Term.eval_binary,ha,hb,op_cast _ _ _ fit]

theorem cut_value {a b : Term W 1 n} {x y : ℕ}
    (ha : a.eval data m v=(x : Word W)) (hb : b.eval data m v=(y : Word W))
    (small : x<2^W) (small' : y<2^W) :
    (Term.select .lt a b (.literal 0) (Term.binary .sub a b)).eval data m v=(x-y : ℕ) := by
  rw [Term.eval_select,ha,hb,test_cast .lt x y small small']
  by_cases h : x<y
  · simp [natTest,h,Nat.sub_eq_zero_of_le h.le]
  · have hy := Nat.le_of_not_gt h
    simp only [natTest,h,decide_false]
    exact binary_value data m v .sub ha hb hy

end ThreeFlat.RAM.TraceBucketAtom

end OAI
