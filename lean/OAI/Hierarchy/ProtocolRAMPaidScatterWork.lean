import OAI.Hierarchy.ProtocolRAMHistogram
import OAI.Hierarchy.ProtocolRAMPaidWidthCore
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # Native expression work of the real sparse width scatter -/
noncomputable section
namespace Hierarchy.ProtocolRAM.PaidWidths
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical

theorem pair_work (s : Slice) (bank : Bank) (edges : ℕ) :
    (pair (s.columns bank edges)).work≤16*s.edge.work+8*s.amount.work+64 := by
  let index:=Expr.lookup s.owner Expr.row
  have first:=Calendar.CatalogueRows.substitute_work (destination bank.base edges s.edge) index
  have second:=Calendar.CatalogueRows.substitute_work s.amount index
  simp only [index,Expr.work,destination] at first second
  dsimp only [pair,Slice.columns,Expr.work,Expr.atRow]
  simp only [destination]
  omega

private theorem lit_scale (n x : ℕ) : (scale n (.lit x)).work=2*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [scale,Expr.work,ih];omega

theorem broadcast_work (n copies : ℕ) (b : Bank) (ball : Expr) :
    (boundedMul n (.lit copies) (.lookup b ball)).work≤1+n*(ball.work+8+2*n) := by
  induction n with
  | zero => simp [boundedMul,Expr.work]
  | succ n ih =>
    simp only [boundedMul,Expr.work,lit_scale]
    rw [Nat.succ_mul]
    nlinarith only [ih]

end Hierarchy.ProtocolRAM.PaidWidths
end

end OAI
