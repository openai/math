import OAI.Hierarchy.DescentSIMDLookup
import OAI.Hierarchy.DescentTerminalSumExpr
import OAI.Hierarchy.DescentTerminalScanFacts

namespace OAI
/-! Exact expression and writable cell of the original terminal scans. -/
namespace Hierarchy
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Fin.CommRing
namespace DescentTerminalVertexFields
theorem sum_read {ι : Type} {c : ℕ} (r : ι→Expr) (m : Memory c) (j : Word c) (amount : ι→ℕ)
    (read : ∀f,(r f).eval m j=(amount f:Word c)) (l : List ι) :
    (sumExpr r l).eval m j=((l.map amount).sum:Word c) := by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp [sumExpr,Expr.eval,RowOp.opcode,BinaryOp.eval,read a,ih,Nat.cast_add]

open DescentSIMDLookup
variable {groups : ℕ}
theorem digit_clip (a n : ℕ) (j : Fin groups) :
    digit a j.val (n%2^(a*groups))=digit a j.val n := by
  unfold digit
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow _ (Nat.mul_le_mul_left _ j.isLt))]

end DescentTerminalVertexFields
namespace DescentTerminalDenseHeaderRAM
variable {bits n : ℕ}
theorem at_image (out : ℕ) (rowExpr : Expr) (m : Memory bits) (i : Fin n) :
    image out n rowExpr m (out+i.val)=rowExpr.eval m (i.val:Word bits) := by
  simp [image,fillSegment,show out+i.val<out+n by omega,Nat.cast_add]

end DescentTerminalDenseHeaderRAM
end Hierarchy

end OAI
