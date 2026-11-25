import OAI.Computability.BorderVNP.CubeTeamRowDispatch
import OAI.Computability.BorderVNP.CubeISAOwnedProgram
import OAI.Computability.BorderVNP.CubeISALocalRowCode

/-! # The concrete owned-group program in the signed evaluator

The row-role scan scatters the incident packet and singleton streams, writes
one triple per owned vertex, recomputes the declared row and checks it. The
directory's frame-46 count is obtained from its final word cursor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA

/-- A strict role scatters its half cube and both singleton orientations, appends
its owned vertex triples, then checks the freshly recomputed declaration row. -/
def strictRole (n b h K s : ℕ) : Code :=
  (OwnedStages.strictSide n b h K s).seq (LocalRow.strictChecked n b h K s)

/-- A repeated-symbol role handles its one singleton orientation and checks
its declared directional lengths. -/
def diagonalRole (n b h K s : ℕ) : Code :=
  (OwnedStages.diagonalSide n).seq (LocalRow.diagonalChecked n b h K s)

/-- Start appending three-word vertex records at the directory pointer in field 78. -/
def startVertices : Code := readFrame 7 62 63 78

/-- Convert the advanced word cursor into a vertex count and publish it in frame 46. -/
def finishVertices : Code := .block [readFrame 54 62 63 78,.binary .sub 55 7 54,
  .constant 56 3,.binary .div 55 55 56,writeFrame 55 62 63 46]

/-- Complete finite native group-stage bytecode used before emitting packet-call identifiers. -/
def ownedGroups (n b h K s : ℕ) : Code := .block [startVertices,
  scan (strictRole n b h K s) (diagonalRole n b h K s),finishVertices]

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
