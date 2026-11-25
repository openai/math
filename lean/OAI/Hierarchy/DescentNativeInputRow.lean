import OAI.Hierarchy.DescentCumulativeInputRows
import OAI.Hierarchy.DescentOrderedOffsetRAM
import OAI.Hierarchy.DescentPortFlowRAM
import Mathlib.Algebra.Order.Floor.Semifield

namespace OAI
/-! # The whole-item row chosen by the installed rotor from its actual weighted prefix -/

namespace Hierarchy.DescentBaseProfile.Cumulative
open DescentOrderedWords
open scoped Classical BigOperators
noncomputable section
variable {I : Type*} [Fintype I] {M Y : ℕ} [NeZero Y] (key : I↪Fin M) (load : I→ℕ)

theorem natural_row_scaled (c : ℝ) (hc : 0<c) (scale : ℕ) (s : I) :
    (row (Y:=Y) key (fun i=>(load i:ℝ)/c) ((scale:ℝ)/c) s).val=
      min (Y*offset key load s/(2*scale)) (Y-1) := by
  have total : prior key (fun i=>(load i:ℝ)/c) s=(offset key load s:ℝ)/c := by
    unfold prior offset
    rw [←Finset.sum_div,Nat.cast_sum]
  change min ⌊(Y:ℝ)*prior key (fun i=>(load i:ℝ)/c) s/(2*((scale:ℝ)/c))⌋₊ _=_
  rw [total]
  have quot : (Y:ℝ)*((offset key load s:ℝ)/c)/(2*((scale:ℝ)/c))=
      ((Y*offset key load s:ℕ):ℝ)/(2*scale:ℕ) := by
    by_cases zero : scale=0
    · simp [zero]
    · push_cast
      field_simp [hc.ne',zero]
  rw [quot,Nat.floor_div_natCast,Nat.floor_natCast]

end
end Hierarchy.DescentBaseProfile.Cumulative

namespace Hierarchy.DescentInputRowRAM
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w : ℕ}

/-- A static number of comparisons suffices. The denominator is read from the
actual stage. A zero-mass suffix at the top threshold is clipped to Y−1. -/
def choose (numerator denominator : Expr) : ℕ→Expr
  | 0=>.lit 0
  | j+1=>.branch .lt numerator (DescentPortFlow.scale denominator (j+1))
      (choose numerator denominator j) (.lit (j+1))

theorem choose_eval (m : Memory w) (r : Word w) (num den : Expr) (x y last : ℕ)
    (readN : num.eval m r=(x:Word w)) (readD : den.eval m r=(y:Word w))
    (hy : 0<y) (boundX : x<2^w) (boundY : last*y<2^w) :
    (choose num den last).eval m r=(min (x/y) last:ℕ) := by
  induction last with
  | zero=>simp [choose,Expr.eval]
  | succ j ih=>
    have prior : j*y<2^w := (Nat.mul_le_mul_right y (Nat.le_succ j)).trans_lt boundY
    simp only [choose,Expr.eval,DescriptorExpr.Comparison.test,decide_eq_true_eq,readN,
      DescentPortFlow.scale_eval,readD,←Nat.cast_mul]
    change (if ((x:Word w).val)<(((j+1)*y:ℕ):Word w).val then _ else _)=_
    rw [Fin.val_cast_of_lt boundX,Fin.val_cast_of_lt boundY]
    by_cases hit : x<(j+1)*y
    · rw [ite_eq_left hit,ih prior]
      have lt: x/y<j+1:= (Nat.div_lt_iff_lt_mul hy).mpr hit
      rw [min_eq_left (by omega),min_eq_left (by omega)]
    · rw [ite_eq_right hit,min_eq_right ((Nat.le_div_iff_mul_le hy).mpr (Nat.le_of_not_gt hit))]

def chooseRow (Y : ℕ) («prefix» available : Expr) :=
  choose (DescentPortFlow.scale «prefix» Y) (.op .add available available) (Y-1)

theorem chooseRow_eval (m : Memory w) (r : Word w) («prefix» available : Expr) (Y mass scale : ℕ)
    (readP : «prefix».eval m r=(mass:Word w)) (readS : available.eval m r=(scale:Word w))
    (pos : 0<scale) (numerator : Y*mass<2^w) (largest : (Y-1)*(2*scale)<2^w) :
    (chooseRow Y «prefix» available).eval m r=(min (Y*mass/(2*scale)) (Y-1):ℕ) := by
  apply choose_eval
  · rw [DescentPortFlow.scale_eval,readP,Nat.cast_mul]
  · change available.eval m r+available.eval m r=_
    simp [readS,two_mul]
  · omega
  · exact numerator
  · exact largest

end
end Hierarchy.DescentInputRowRAM

end OAI
