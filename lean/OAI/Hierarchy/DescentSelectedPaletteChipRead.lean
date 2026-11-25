import OAI.Hierarchy.DescentOrdinaryMountedBirth
import OAI.Hierarchy.DescentSelectedPaletteChipBits

namespace OAI
/-! # The mounted newborn chip has the original donor bits -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentSIMDLookup DescentRawCablePanel DescentOrdinaryBorn
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (E : ArgumentEntry v)

/-- The casting of the source's host, group and word width preserves the
value of the packed chip at that exact row. -/
theorem native_chip_material (birth : E.BirthShape v)
    (parts : Fin E.clip.venue.hosts→Fin E.clip.venue.groups→DepotRAM.Parts E.clip.venue.socket)
    (h : Fin v.bornBook.hosts) (g : Fin v.bornBook.groups)
    (fmt : DepotRAM.Shape) (mat : DepotRAM.Parts fmt) (profile slots : ℕ)
    (socket : E.clip.venue.socket=fmt) (profileEq : E.clip.venue.profile=profile)
    (slotsEq : E.clip.venue.slots=slots)
    (mounted : HEq (parts (h.cast birth.hosts) (g.cast birth.groups)) mat) :
    (E.nativeChips v birth parts h g).val=(DepotRAM.chip fmt fmt.cap profile v.gadget.b slots mat).val:=by
  subst fmt;subst profile;subst slots
  obtain rfl:=eq_of_heq mounted
  rfl

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
