import OAI.Computability.BorderVNP.CubeISAOwnedStrictScatter
import OAI.Computability.BorderVNP.CubeISAOwnedVertexRow

/-! # Concrete programs for each incident side of a team-owned row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

/-- One incident side of a strict symbol pair. Scatter the native packets and
both singleton orientations, then append the owned vertices to the directory. -/
def strictSide (n b h K s : ℕ) : Code :=
  .seq (strictScatter n b h K s) (.seq (OwnedRowSetup.packet n b h K s) (OwnedVertex.vertexRow n))

/-- An equal-symbol row has one ordered singleton pass. -/
def diagonalSide (n : ℕ) : Code := singleStage n

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI
