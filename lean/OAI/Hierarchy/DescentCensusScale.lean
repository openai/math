import OAI.Hierarchy.DescentWordProduct

namespace OAI
/-! # Scaling native row expressions by public constants -/

namespace Hierarchy.DescentSixParty.MarkedCensus
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM.DescriptorExpr
open scoped Fin.CommRing Classical BigOperators
noncomputable section

/-- Multiplying a measured row by an arbitrary public constant uses one
mask and a conditional fixed literal per significant input bit. -/
def contribution (c j : ℕ) (x : Expr) : Expr :=
  .branch .eq (.op .mask x (.lit (2^j))) (.lit 0) (.lit 0) (.lit (c*2^j))

def scale (c : ℕ) (x : Expr) : ℕ→Expr
  | 0 => .lit 0
  | t+1 => .op .add (scale c x t) (contribution c t x)

theorem contribution_eval {w j : ℕ} (c : ℕ) (x : Expr) (m : Memory w) (i : Word w) (h : j<w) :
    (contribution c j x).eval m i=(c:Word w)*((2^j*((x.eval m i).val/2^j%2):ℕ):Word w) := by
  let y:=x.eval m i
  change (if Comparison.eq.test (BinaryOp.bitAnd.eval y ((2^j:ℕ):Word w)) 0 then 0 else ((c*2^j:ℕ):Word w))=_
  change (if (BinaryOp.bitAnd.eval y ((2^j:ℕ):Word w) == 0) = true then 0 else ((c*2^j:ℕ):Word w))= (c:Word w)*((2^j*(y.val/2^j%2):ℕ):Word w)
  by_cases hz : y.val/2^j%2=0
  · have off:=(DescentWordProduct.bitTest y h).2 hz
    have yes : (BinaryOp.bitAnd.eval y ((2^j:ℕ):Word w) == 0) = true := beq_iff_eq.mpr off
    rw [ite_eq_left yes,hz]
    simp
  · have on : BinaryOp.bitAnd.eval y ((2^j:ℕ):Word w)≠0 := fun eqn=>hz ((DescentWordProduct.bitTest y h).1 eqn)
    have one : y.val/2^j%2=1 := by omega
    have neq : (BinaryOp.bitAnd.eval y ((2^j:ℕ):Word w) == 0) ≠ true := by simpa using on
    rw [ite_eq_right neq,one]
    simp

theorem scale_eval {w : ℕ} (c : ℕ) (x : Expr) (m : Memory w) (r : Word w) (t : ℕ) (ht : t≤w) :
    (scale c x t).eval m r=(c:Word w)*(((x.eval m r).val%2^t:ℕ):Word w) := by
  induction t with
  | zero => simp [scale,Expr.eval,Nat.mod_one]
  | succ t ih =>
    rw [scale,Expr.eval,ih (by omega),contribution_eval _ _ _ _ (by omega),Nat.mod_pow_succ]
    simp [RowOp.opcode,BinaryOp.eval,mul_add]

@[simp] theorem full_scale {w : ℕ} (c : ℕ) (x : Expr) (m : Memory w) (r : Word w) :
    (scale c x w).eval m r=(c:Word w)*x.eval m r := by
  rw [scale_eval _ _ _ _ _ le_rfl,Nat.mod_eq_of_lt (x.eval m r).isLt]
  simp

theorem scale_fits {w a : ℕ} (c : ℕ) (x : Expr) (good : x.Fits w a) (t : ℕ) :
    (scale c x t).Fits w a := by
  induction t with
  | zero => trivial
  | succ t ih => exact ⟨ih,⟨good,trivial⟩,trivial,trivial,trivial⟩

theorem scale_work (c : ℕ) (x : Expr) (t : ℕ) : (scale c x t).work=1+t*(x.work+7) := by
  induction t with
  | zero => simp [scale,Expr.work]
  | succ t ih => simp only [scale,contribution,Expr.work,ih,Nat.succ_mul];omega

end
end Hierarchy.DescentSixParty.MarkedCensus

end OAI
