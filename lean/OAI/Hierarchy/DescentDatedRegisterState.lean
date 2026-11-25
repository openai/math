import OAI.Hierarchy.DescentPriorResetArchive
import OAI.Hierarchy.DescentPhysicalResetDate
import OAI.Hierarchy.DescentInitialDatePorts
import OAI.Hierarchy.DescentDatedOrdinaryVenueModel

namespace OAI
/-! # The public registers at the cut between two consecutive native dates -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentInitialHost DescentCompiler
open DescentDatedSeedStartup DescentDatedSeedStartup.Input DescentColonies DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section
namespace DatePorts
def ordinary {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) : DatePorts:=
  ⟨PriorResetArchive.ordinary v floor,v.venue,v.venue.operands (v.reachedSources floor) (v.rasterEnd floor),
    v.resolver.size+2,v.resolver.lanes,v.resolver.operands,v.resolver.nodes,v.palette.nextLanes,v.resolver.hosts,v.paletteShape.primitiveBits⟩

def reset {w : ℕ} (a : PhysicalReset) (floor : ℕ) (u : a.DateInputs floor w) : DatePorts:=
  let v:=a.successor
  let base:=a.rebased floor
  let x:=v.fundedEnd base
  let B:=v.venue.sources (PhysicalReset.FinalInputs.predecessor u) x
  ⟨PriorResetArchive.reset v base,v.venue.next,v.venue.next.operands B (v.venue.venueStart x),
    v.nodeBits,v.receiver.lanes,v.argumentSlots,v.nodes,v.primitive.chart.lanes,v.sheets.hosts,v.primitive.chart.bits⟩

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
