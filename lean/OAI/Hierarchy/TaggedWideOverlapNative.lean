import OAI.Hierarchy.TaggedWideOverlap
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Runtime generation of the three passive-overlap barrel controls -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Overlap
open Tagged.PassiveWindow Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing

def diff (a b : Expr) : Expr := .branch .lt a b (.lit 0) (.op .sub a b)
def small (a b : Expr) : Expr := .branch .lt a b a b
def large (a b : Expr) : Expr := .branch .lt a b b a

structure Fields where
  start : Expr
  width : Expr
  low : Expr
  opposite : Expr

def lower (a : Fields) := diff a.start a.low
def upper (a : Fields) := diff (.op .add a.start a.width) a.low
def start (a b : Fields) := large (lower a) (lower b)
def length (a b : Fields) : Expr :=
  .branch .eq a.opposite b.opposite (diff (small (upper a) (upper b)) (start a b)) (.lit 0)
def head (W : ℕ) (a b c : Fields) := small (.lit W) (diff (.op .add (start a b) c.low) c.start)

variable {w : ℕ} (m : Memory w) (r : Word w)

private theorem subtract (a b : Expr) : ((diff a b).eval m r).val=(a.eval m r).val-(b.eval m r).val := by
  by_cases h : a.eval m r < b.eval m r
  · have le : (a.eval m r).val ≤ (b.eval m r).val := h.le
    simp [diff,Expr.eval,Comparison.test,h,Nat.sub_eq_zero_of_le le]
  · have le : b.eval m r ≤ a.eval m r := le_of_not_gt h
    simp [diff,Expr.eval,Comparison.test,h,RowOp.opcode,BinaryOp.eval,Fin.sub_val_of_le le]

private theorem minimum (a b : Expr) : ((small a b).eval m r).val=min (a.eval m r).val (b.eval m r).val := by
  by_cases h : a.eval m r < b.eval m r
  · have le : (a.eval m r).val ≤ (b.eval m r).val := h.le
    simp [small,Expr.eval,Comparison.test,h,min_eq_left le]
  · have le : (b.eval m r).val ≤ (a.eval m r).val := le_of_not_gt h
    simp [small,Expr.eval,Comparison.test,h,min_eq_right le]

private theorem maximum (a b : Expr) : ((large a b).eval m r).val=max (a.eval m r).val (b.eval m r).val := by
  by_cases h : a.eval m r < b.eval m r
  · have le : (a.eval m r).val ≤ (b.eval m r).val := h.le
    simp [large,Expr.eval,Comparison.test,h,max_eq_right le]
  · have le : (b.eval m r).val ≤ (a.eval m r).val := le_of_not_gt h
    simp [large,Expr.eval,Comparison.test,h,max_eq_left le]

def slice (a : Fields) : Slice := ⟨(a.start.eval m r).val,(a.width.eval m r).val,(a.low.eval m r).val⟩

private theorem start_value (a b : Fields) : ((start a b).eval m r).val=lo (slice m r a) (slice m r b) := by
  simp only [start,maximum,lower,subtract,slice,lo]

private theorem addValue (a b : Expr) (room : (a.eval m r).val+(b.eval m r).val<2^w) :
    ((Expr.op .add a b).eval m r).val=(a.eval m r).val+(b.eval m r).val := by
  simp only [Expr.eval,RowOp.opcode,BinaryOp.eval,Fin.val_add,Nat.mod_eq_of_lt room]

theorem length_value (a b : Fields)
    (aFit : (a.start.eval m r).val+(a.width.eval m r).val<2^w)
    (bFit : (b.start.eval m r).val+(b.width.eval m r).val<2^w) :
    ((length a b).eval m r).val=
      if a.opposite.eval m r=b.opposite.eval m r then span (slice m r a) (slice m r b) else 0 := by
  have test (a b c d : Expr) : (Expr.branch .eq a b c d).eval m r =
      (if a.eval m r = b.eval m r then c.eval m r else d.eval m r) := by
    simp [Expr.eval,Comparison.test]
  have top (c : Fields) (fit : (c.start.eval m r).val+(c.width.eval m r).val<2^w) :
      ((upper c).eval m r).val=(c.start.eval m r).val+(c.width.eval m r).val-(c.low.eval m r).val := by
    rw [upper,subtract,addValue m r _ _ fit]
  unfold length
  rw [test]
  by_cases same : a.opposite.eval m r = b.opposite.eval m r
  · simp only [ite_eq_left same,subtract,minimum,top a aFit,top b bFit,start_value]; rfl
  · simp only [ite_eq_right same]; rfl

theorem head_value (W : ℕ) (a b : Fields) (side : Bool) (smallW : W<2^w)
    (room : lo (slice m r a) (slice m r b)+((if side then b else a).low.eval m r).val<2^w) :
    ((head W a b (if side then b else a)).eval m r).val=
      min W (offset (slice m r a) (slice m r b) side) := by
  have fits : ((start a b).eval m r).val+((if side then b else a).low.eval m r).val<2^w := by
    rwa [start_value]
  have lit : ((Expr.lit W).eval m r).val=W := Fin.val_cast_of_lt smallW
  rw [head,minimum,subtract,addValue m r _ _ fits,start_value,lit]
  cases side <;> rfl

end Hierarchy.ProtocolRAM.Overlap

end
end OAI
