import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Native expression for multiplying a row word by a fixed natural -/
namespace Hierarchy.DescentPortFlow
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing
noncomputable section

variable {w : ℕ}

def scale (x : Expr) : ℕ→Expr
  | 0=>.lit 0
  | t+1=>.op .add (scale x t) x

theorem scale_eval (x : Expr) (t : ℕ) (m : Memory w) (j : Word w) :
    (scale x t).eval m j=(t:Word w)*x.eval m j := by
  induction t with
  | zero=>simp [scale,Expr.eval]
  | succ t ih=>simp [scale,Expr.eval,RowOp.opcode,BinaryOp.eval,ih,Nat.cast_succ,add_mul]

theorem scale_fits (x : Expr) (t : ℕ) {first : ℕ} (fit : x.Fits w first) : (scale x t).Fits w first := by
  induction t with
  | zero=>trivial
  | succ t ih=>exact ⟨ih,fit⟩

@[simp] theorem scale_work (x : Expr) (t : ℕ) : (scale x t).work=1+t*(x.work+1) := by
  induction t with
  | zero=>simp [scale,Expr.work]
  | succ t ih=>simp [scale,Expr.work,ih,Nat.succ_mul,Nat.add_assoc]

end
end Hierarchy.DescentPortFlow

end OAI
