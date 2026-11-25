import OAI.Computability.BorderVNP.CubeTeamRowClockEventually
import OAI.Computability.BorderVNP.CubeISAOwnedDoubleStage
import OAI.Computability.BorderVNP.CubeISAOwnedVertexStage

/-! # Identification of the accepted row clock with the assembled native stages -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRowClock

open RoutingISA RoutingISA.OwnedStages Physical

variable {n d blocks b h K s : ℕ}

/-- Charged ticks of the concrete local strict-row check, including the swap
which restores the sorted endpoint registers. -/
def strictCheckTicks (i : Fin (n+1)) (sym : Symbols d) (blocks b h K s : ℕ) :=
  (LocalRow.setup n b h K s).slots + (4*(n+1)+1) + DeclaredRow.strictCost i sym blocks b K h +
    3 + LocalRow.finish.slots + ((n+1)*(CubeLengths.rowBody.slots+1)+1)

/-- The diagonal check has one ordered scalar pass and leaves the symbol pair in place. -/
def diagonalCheckTicks (i : Fin (n+1)) (u : Fin d) (blocks b h K s : ℕ) :=
  (LocalRow.setup n b h K s).slots + (4*(n+1)+1) +
    (4+SingleTally.rowCost i u u (blocks*(h*b))) +
    LocalRow.finish.slots + ((n+1)*(CubeLengths.rowBody.slots+1)+1)

private theorem singleStage_ticks (D : Scatter.SingleRowData n d (blocks*(h*b))) :
    singleStageCost D = OwnedRowSetup.single.slots + singleTicks blocks (h*b) D.axis D.left D.right := rfl

/-- Both local sides of a strict pair have the cost of the actual packet stage,
the two initialized singleton stages with their swaps, the vertex stage, and the
local strict declaration check. -/
theorem strict_stage_cost (i : Fin (n+1)) (sym : Symbols d)
    (first second : Scatter.SingleRowData n d (blocks*(h*b)))
    (axis : first.axis = i ∧ second.axis = i) (left : first.left = sym.val.1 ∧ second.left = sym.val.2)
    (right : first.right = sym.val.2 ∧ second.right = sym.val.1) :
    let ticks := (packetStageCost n d blocks b h K s +
      (singleStageCost first + (3+(singleStageCost second+3))) + vertexStageCost n d blocks b h K s) +
      strictCheckTicks i sym blocks b h K s
    physicalRoleTicks blocks b h K s i sym.val.1 sym.val.2 = ticks ∧
      physicalRoleTicks blocks b h K s i sym.val.2 sym.val.1 = ticks := by
  dsimp only
  have pk : packetStageCost n d blocks b h K s =
      (OwnedRowSetup.packet n b h K s).slots + packetTicks n d blocks b h K s := rfl
  have vertex : vertexStageCost n d blocks b h K s = (OwnedRowSetup.packet n b h K s).slots +
      packetScan n d blocks (2+OwnedVertex.emitPacketCost n (Tally.selectorWidth n K h)) := rfl
  rw [pk,vertex,singleStage_ticks first,singleStage_ticks second,axis.1,axis.2,left.1,left.2,right.1,right.2]
  obtain ⟨t1,t2⟩ := tallyTicks_strict blocks b h K i sym
  simp only [physicalRoleTicks,checkedRoleTicks,strictSetupSlots,scatterRoleTicks,vertexTicks,
    strictCheckTicks,sym.property.ne,sym.property.ne',ite_false,t1,t2]
  constructor <;> omega

/-- A repeated-symbol pair has one initialized singleton stage and one local
diagonal declaration check, independent of the unvisited packet directory. -/
theorem diagonal_stage_cost (i : Fin (n+1)) (u : Fin d) (row : Scatter.SingleRowData n d (blocks*(h*b)))
    (axis : row.axis = i) (left : row.left = u) (right : row.right = u) :
    physicalRoleTicks blocks b h K s i u u = singleStageCost row + diagonalCheckTicks i u blocks b h K s := by
  rw [singleStage_ticks,axis,left,right]
  simp only [physicalRoleTicks,checkedRoleTicks,scatterRoleTicks,tallyTicks,vertexTicks,diagonalCheckTicks,ite_true]
  omega

end Cube.TeamRowClock

end BorderVNP
end Computability
end OAI
