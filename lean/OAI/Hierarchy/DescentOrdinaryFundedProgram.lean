import OAI.Hierarchy.DescentOrdinaryProgramBlocks
import OAI.Hierarchy.DescentOrdinaryVenueCalendarRead
import OAI.Hierarchy.DescentDatedOrdinaryFundedRaster

namespace OAI
/-! # Printed funded census at the public ordinary date -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentPackedColony
open DescentPaidResidentCount StageVenueTail ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
namespace FundedProgram
variable (a:Dated.Ordinary)(d:Date)(work start material:ℕ)(field:Bank)
variable (ports:Ports (OrdinaryRaster.paths a))(i:Dated.Operands)
local notation "p" => OrdinaryRaster.shapes a
local notation "paths" => OrdinaryRaster.paths a
local notation "n" => OrdinaryRaster.nameBits a
local notation "b" => d.paidBits
local notation "old" => a.lanesAt
local notation "prep" => OrdinaryRaster.prepared a d work start
local notation "stop" => OrdinaryRaster.sweep a d work start
local notation "labels" => fun l:Fin p=>DescentSharedCableNames.Packed.token (some l)

def banks:DescentOrdinaryRasterReturn.Sources:=
  ⟨Sweep.paidBank prep p (paths*2^a.k) a.cap b n a.H a.G work,
   Sweep.aliveBank prep p (paths*2^a.k) a.cap b n a.H a.G work,
   DescentOrdinaryPeerCount.newCount material a.H a.D d.hosts d.degree⟩

/-- Includes the retained fields, real old count repitch, both sweeps and both dense rasters. -/
def atAge (w:ℕ):PrintedStep w:=
  let s:=Sweep.HeldRepacked.program start a.H a.G old work a.k paths a.cap b n p field ports i.atoms labels w
  let t:=Sweep.HeldRepacked.ticks start a.H a.G old work a.k paths a.cap b n p field ports i.atoms labels w
  let r:=DescentOrdinaryRasterReturn.phase (OrdinaryRaster.dims a d work) (banks a d work start material) stop w
  ⟨s.seq r.program,t+r.ticks⟩

def fromChart (c:OrdinaryReturn)(donor:ℕ)(field:Bank)(ports:Ports (OrdinaryRaster.paths c.area))
    (input:Dated.Operands)(w:ℕ):PrintedStep w:=
  atAge c.area c.venue c.work (c.resultEnd donor) (c.materialEnd donor) field ports input w

end FundedProgram
namespace PhysicalOrdinary
attribute [local irreducible] Sweep.HeldRepacked.program Sweep.HeldRepacked.ticks
  DescentOrdinaryRasterReturn.phase DescentOrdinaryPeerCount.newCount
variable {F P:Type} [Field F](v:PhysicalOrdinary F P)(floor:ℕ)(B:v.FundedInputs)(input:Dated.Operands)
theorem funded_printed {w:ℕ}(ok:v.FundedRoom floor B input w):
    PrintedStep.ofPhase (v.fundedRaster floor B input w ok)=
      FundedProgram.atAge v.area v.venue v.rasterLanes (v.endAddress floor) (v.materialEnd floor)
        B.field B.ports input w:=rfl

theorem funded_calendar {w:ℕ}(ok:v.FundedRoom floor B input w):
    PrintedStep.ofPhase (v.fundedRaster floor B input w ok)=
      FundedProgram.fromChart v.returnChart (v.donorEnd floor) B.field B.ports input w:=rfl

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI
