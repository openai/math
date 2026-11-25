import OAI.Hierarchy.DescentDatedSignedAfterMark
import OAI.Hierarchy.DescentIssuedSignedChart

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local DescentSIMDLookup ProtocolRAM
noncomputable section
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
local notation "phys.signedPhase" => v.withIssuedSigned.signedPhase
local notation "chart" => v.issuedSignedChart

def signedReturn (floor:ℕ) (input:Stage.Dated.Operands) (count parts adj:Bank) (w:ℕ):NativePhase w:=(v.signedPredecessor floor input count parts adj w).seq
  (phys.signedPhase floor chart w)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
