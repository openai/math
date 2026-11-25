import OAI.Hierarchy.DescentDonorShapeFields
import OAI.Hierarchy.DescentMatcherRateNumbers
import OAI.Hierarchy.DescentSignedCableFields
import OAI.Hierarchy.DescentHaloWalkRAM

namespace OAI
/-! # Numerical widths of the retained donor fields -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Owners
def inputBits (r D p d : ℕ) := 1+d*fields r D p
def digits (r D d : ℕ) := max d (Nat.clog 2 (max r D+1))
end Hierarchy.DescentPacking.PackedMatch.Local.Owners

namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentPacking.PackedMatch.Local DescentSharedCableNames DescentHaloWalkRAM
variable (s : Shape)
def rawBits := Owners.inputBits s.blocks s.degree (2*s.cap) s.short
def freshBits := s.widths*((s.blocks*s.cap)*8)
def cableBits := DescentSignedCableCodec.width s.degree s.cap*(s.blocks*(2*s.cap))
def ownerBits := ((Owners.digits s.blocks s.degree s.short*3)*s.blocks)*(s.degree+1)
def chartBits := Packed.bits (breadth s.degree)*breadth s.degree
def totalBits := ((rawBits s+cableBits s)+(ownerBits s+chartBits s))+(chartBits s+freshBits s)

end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
