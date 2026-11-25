import OAI.Hierarchy.DescentDonorWidths
import OAI.Hierarchy.DescentDonorShape
import OAI.Hierarchy.DescentPackedOwnerWord
import OAI.Hierarchy.DescentSignedCableFields
import OAI.Hierarchy.DescentHaloWalkRAM
import OAI.Hierarchy.DescentPackedMatchShape

namespace OAI
/-! # Sizes of the stored old cable, owner and issued birth fields -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentPacking.PackedMatch.Local DescentSharedCableNames DescentHaloWalkRAM

variable (s : Shape)
namespace Fresh
variable (z : DescentPacking.PackedMatch.Shape)

/-- The extra bit per lane pays for the actual active-lane prefix. -/
def laneWidth := 1+rawBits s+z.outputBits+(z.digit+1)*(z.pairs*6)

end Fresh
end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
