import OAI.Hierarchy.DescentSignedProgram
import OAI.Hierarchy.DescentDatedMaterialForward
import OAI.Hierarchy.DescentDatedPriorHeaderPorts
import OAI.Hierarchy.DescentDatedOrdinarySignedInvoice
import OAI.Hierarchy.DescentOrdinaryMarkPhase
import OAI.Hierarchy.DescentOrdinaryPeerRows

namespace OAI
/-! Address every original input to the signed ordinary date in genuine preceding phases. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony
open DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
/-- Equalities of the public dimensions chosen before inspecting memory. -/
structure SignedChart : Prop where
  degree:v.signed.degree=(v.ticket.depotShape v.short).degree
  blocks:v.signed.blocks=(v.ticket.depotShape v.short).blocks
  seats:v.signed.residentSlots=DepotRAM.Material.roles (v.ticket.depotShape v.short)
  markSlots:v.signed.residentSlots=v.markShape.slots

namespace SignedChart
variable {v} (c:v.SignedChart)
def donorSeat (o:Fin v.signed.residentSlots):DepotRAM.Material.Seat (v.ticket.depotShape v.short):=
  (DepotRAM.Material.seatIndex (v.ticket.depotShape v.short)).symm (Fin.cast c.seats o)
def ray (o:Fin v.signed.reach):Fin (breadth (v.ticket.depotShape v.short).degree):=Fin.cast (congrArg breadth c.degree) o
end SignedChart

variable (floor:ℕ) (c:v.SignedChart)
local notation "header"=>v.donorEnd floor
local notation "begin₀"=>v.materialStart floor
local notation "geo"=>PriorHeader.rankBanks v.area.H v.signed.groups v.signed.lanes v.signed.degree header
local notation "raw"=>PriorHeader.ports v.area.H v.signed.groups v.signed.lanes v.signed.degree header
def signedProgram : SignedProgram :=
  ⟨v.signed,v.materialProgram,v.markShape,v.area.H,v.area.D,v.venue.hosts,v.venue.degree,v.donorEnd floor⟩

include c in
theorem publicSignedChart : (v.signedProgram floor).Chart :=
  ⟨c.degree,c.blocks,c.seats,c.markSlots⟩

def signedInput:v.signed.Input:=(v.signedProgram floor).input (v.publicSignedChart floor c)

theorem signed_work:v.signed.SnippetWork (v.signedInput floor c) (max v.venue.degree 88):=by
  refine ⟨Nat.le_max_left ..,?_,?_,?_,?_,?_,?_⟩
  · intro z;exact (v.socket_work ..).le.trans (Nat.le_max_right ..)
  · intro z side;exact (v.socket_work ..).le.trans (Nat.le_max_right ..)
  · intro z f;exact (v.socket_work ..).le.trans (Nat.le_max_right ..)
  · intro z;apply Nat.le_trans (m:=88) _ (Nat.le_max_right ..);change 22≤88;decide
  · intro x o;apply Nat.le_trans (m:=88) _ (Nat.le_max_right ..);change 12≤88;decide
  · intro x o;apply Nat.le_trans (m:=88) _ (Nat.le_max_right ..);change 12≤88;decide

def signedPhase (w:ℕ):NativePhase w:=v.signed.phase (v.signedInput floor c) (v.markEnd floor) w

theorem signed_price (w:ℕ):
    (v.signedPhase floor c w).ticks ≤ v.signed.fixedTime (max v.venue.degree 88) ∧
    DescentStaticWordColumn.names (v.signedPhase floor c w).program ≤ v.signed.fixedNames (max v.venue.degree 88):=
  v.signed.fixed_cost (v.signedInput floor c) (v.markEnd floor) w (max v.venue.degree 88) (v.signed_work floor c)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
