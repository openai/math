import OAI.Hierarchy.ProtocolRAMFinalInstalledWidths
import OAI.Hierarchy.ProtocolRAMPaidScatterWork

namespace OAI
/-! # Native expression work of all five issued sparse-width column types -/
noncomputable section
namespace Hierarchy.ProtocolRAM.PaidWidths
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram Calendar.StockCommit
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical

def issueWork (operands maxBits : ℕ) := 16*operands+8*(operands+12+maxBits*(operands+8+2*maxBits))+64

theorem direct_work (a : Area) (s : Sources) (g : LabelSource) (bank : Bank) (edges u n : ℕ)
    (edge : g.edge.work≤u) : (pair ((paidDirect a s g).columns bank edges)).work≤ issueWork u n := by
  apply (pair_work ..).trans
  change 16*g.edge.work+8*7+64≤_
  unfold issueWork
  omega

theorem mate_work (a : Area) (s : Sources) (mask edge : Expr) (bank : Bank) (edges u n : ℕ)
    (ma : mask.work≤u) (ed : edge.work≤u) :
    (pair ((paidMate a s mask edge).columns bank edges)).work≤ issueWork u n := by
  apply (pair_work ..).trans
  change 16*edge.work+8*(mask.work+1+1+7+1)+64≤_
  unfold issueWork
  omega

theorem tree_work (a : Area) (positions : ℕ) (owner parity bank : Bank) (edge ball : Expr)
    (copies edges u n : ℕ) (ed : edge.work≤u) (bl : ball.work≤u) :
    (pair ((paidBroadcast a positions owner parity edge ball copies n).columns bank edges)).work≤ issueWork u n := by
  apply (pair_work ..).trans
  have bound:=broadcast_work n copies (archivedBank a.broadcast a.rows) ball
  have mul:=Nat.mul_le_mul_left n (Nat.add_le_add_right (Nat.add_le_add_right bl 8) (2*n))
  change 16*edge.work+8*(boundedMul n (.lit copies) (.lookup (archivedBank a.broadcast a.rows) ball)).work+64≤_
  unfold issueWork
  omega

theorem spill_work (positions : ℕ) (owner parity saved bank : Bank) (edge good : Expr)
    (edges u n : ℕ) (ed : edge.work≤u) (gd : good.work≤u) :
    (pair ((spill positions owner parity saved edge good).columns bank edges)).work≤ issueWork u n := by
  apply (pair_work ..).trans
  change 16*edge.work+8*(good.work+5)+64≤_
  unfold issueWork
  omega

end Hierarchy.ProtocolRAM.PaidWidths
end

end OAI
