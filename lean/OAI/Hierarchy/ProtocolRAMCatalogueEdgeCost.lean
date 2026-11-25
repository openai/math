import OAI.Hierarchy.ProtocolRAMCatalogueEdgeID
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # Native work and operand bounds of the true original-edge lookup -/

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows

def edgeWork (source flags : ℕ) := 8*(source+1)+(source+3)*flags+8

theorem Board.checkedEdge_work (b : Board) (e : Expr) :
    (b.checkedEdge e).work ≤ edgeWork e.work b.bought.flag.work := by
  have sub:=substitute_work b.bought.flag (.op .sub e (.lit b.coreRows))
  change (b.bought.flag.atRow (.op .sub e (.lit b.coreRows))).work ≤
    b.bought.flag.work * (e.work + 3) at sub
  simp only [Board.checkedEdge, Expr.work, edgeWork]
  rw [Nat.mul_comm (e.work+3) b.bought.flag.work]
  omega

theorem Board.commonID_work (b : Board) (e : Expr) :
    (b.commonID e).work≤2+edgeWork e.work b.bought.flag.work := by
  have h:=b.checkedEdge_work e
  change 1+(b.checkedEdge e).work+1≤_
  omega

theorem Board.checkedEdge_fits (b : Board) (e : Expr) {w limit : ℕ} (hf : b.bought.flag.Fits w limit)
    (he : e.Fits w limit) : (b.checkedEdge e).Fits w limit :=
  ⟨he,trivial,he,he,trivial,⟨fits_atRow _ _ hf ⟨he,trivial⟩,trivial,trivial,he⟩,trivial⟩

theorem Board.commonID_fits (b : Board) (e : Expr) {w limit : ℕ} (hf : b.bought.flag.Fits w limit)
    (he : e.Fits w limit) : (b.commonID e).Fits w limit := ⟨trivial,b.checkedEdge_fits e hf he⟩

theorem Board.originalProbe_work (b : Board) (stride birth : ℕ) (ball : Expr) :
    (b.originalProbe stride birth ball).work=ball.work+2 := by simp [originalProbe,Expr.work];omega

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end OAI
