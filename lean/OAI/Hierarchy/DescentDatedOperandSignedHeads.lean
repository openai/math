import OAI.Hierarchy.DescentDatedOperandOriginalHeads
import OAI.Hierarchy.DescentDatedSignedParentHeads

namespace OAI
/-! # Original signed-pitch source expressions at every candidate, including the retained parent -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentHaloWalkRAM DescentSIMDLookup DescentSharedCableNames DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "P" => breadth (DepotRAM.Shape.degree (v.ticket.depotShape v.short))
local notation "O" => DepotRAM.Material.roles (v.ticket.depotShape v.short)

def localRankHead (floor : ℕ) (p : Fin P) : Expr :=
  let pub:=DescentDatedSourcePathDirectory.hostEnd (v.operandPathStart floor) (e).oldHosts (fmt).degree
  let chart:=DescentDatedSourcePathDirectory.Local.chart pub (v.operandRankStart floor) (e).oldHosts (e).groups (e).lanes p
  DepotRAM.Material.Route.lift (v.receiverMap floor) ((e).oldHosts*chunks (e).groups (e).lanes)
    (DescentSharedLeafLookup.source chart (0:Fin 1))

def signedRawHead (floor : ℕ) (c : v.SignedChart) (block : Fin (e).blocks) (f : Fin 8) (i : Fin (P*O)) : Expr :=
  if live:f.val<6 then v.rawFieldHead floor block ⟨f.val,live⟩ i
  else if f.val=6 then v.parentSerial floor c block i else v.parentPeer floor c block i

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
