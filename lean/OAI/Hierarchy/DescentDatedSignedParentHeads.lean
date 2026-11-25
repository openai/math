import OAI.Hierarchy.DescentDatedSignedInput

namespace OAI
/-! The retained parent supplies its signed rank and peer expressions at each physical candidate. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentHaloWalkRAM DescentSIMDLookup DescentSharedCableNames DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
local notation "e" => v.material
local notation "s" => v.signed
local notation "fmt" => v.ticket.depotShape v.short
local notation "P" => breadth (DepotRAM.Shape.degree (v.ticket.depotShape v.short))
local notation "O" => DepotRAM.Material.roles (v.ticket.depotShape v.short)

def parentSlot (c : v.SignedChart) (i : Fin (P*O)) : Fin (s).candidates :=
  i.cast (congrArg₂ Nat.mul (congrArg breadth c.degree.symm) c.seats.symm)
def parentSerial (floor : ℕ) (c : v.SignedChart) (x : Fin (e).blocks) (i : Fin (P*O)) : Expr :=
  let core:=DescentOrdinarySignedParents.ROM.endAddress ((s).tailStart (v.markEnd floor)) (s).degree (s).lowSites
    (s).tickets (s).cap (s).fieldBits (s).lanes
  DescentOrdinarySignedAll.ranks core (s).blocks (s).candidates (s).fieldBits (s).lanes (s).hosts (s).groups
    (x.cast c.blocks.symm) 1 (v.parentSlot c i)
def parentPeer (floor : ℕ) (c : v.SignedChart) (x : Fin (e).blocks) (i : Fin (P*O)) : Expr :=
  (s).peerField (v.signedInput floor c) (v.markEnd floor) (x.cast c.blocks.symm,v.parentSlot c i)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
