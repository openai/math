import OAI.Hierarchy.DescentRegisteredOrdinaryStep
import OAI.Hierarchy.DescentPublicSignedProgram

namespace OAI
/-! # Public geometric observations used when erasing a named ordinary ticket -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM
noncomputable section
structure StaticCore where
  donor : DonorDate
  format : DepotRAM.Shape
  area : Dated.Ordinary
  signed : SignedExtent
  material : MaterialExtent
  donorEnd : ℕ
  prefixProgram : SignedProgram
  measures : Dated.Measures

variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
def staticCore (floor : ℕ) : StaticCore :=
  ⟨v.ticket.donorDate,v.ticket.depotShape v.short,v.area,v.signed,v.material,
    v.donorEnd floor,v.signedProgram floor,
    ⟨v.prior.placement.wire,v.prior.placement.z,v.prior.placement.hist⟩⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
