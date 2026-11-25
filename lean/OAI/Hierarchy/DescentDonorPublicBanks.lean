import OAI.Hierarchy.DescentResidentDonorClock
import OAI.Hierarchy.DescentReadyGeometryPhase
import OAI.Hierarchy.DescentDepotZipInstall
import OAI.Hierarchy.DescentDonorFreshTables

namespace OAI
/-! # The donor's fixed prior storage interface and numeric public address book -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentHostDegree DescentRawCablePanel DescentSIMDLookup DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM DescentPackedZip DescentPackedColony
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option quotPrecheck false
/-- All these «fields» are earlier literal bank addresses of the prior matcher.
The destination layout and its contents are derived below. -/
structure PriorBanks (r D B K : ℕ) where
  gate : Bank
  hub : Bank
  peers : Ports D
  winners : Fin r→Bank
  marked : Fin r→Fin (2*B)→Bank
  signed : Fin r→Fin (2*B)→Bank
  operands : Fin («fields» r D (2*B))→Tables
  topology : Bank
  born : Bank

/-- Fixed predecessor storage, evaluated at the public cohort size of this date. -/
abbrev PriorSource := ∀ blocks degree cap count : ℕ,PriorBanks blocks degree cap count

section
variable (fmt : DepotRAM.Shape) (s : DescentPacking.PackedMatch.Shape) (K₀ H J M amount rootAt second leaf : ℕ)
variable (old : PriorBanks fmt.blocks fmt.degree fmt.cap K₀)
local notation "rows" => H*chunks J M
local notation "venuePlan" => DepotRAM.Resident.Dynamic.Placement.layout H J M fmt.degree (DepotRAM.rawBits fmt) rootAt old.peers.roster old.hub

def publicAddressed : DepotRAM.Resident.Addressed fmt K₀ where
  layout:=⟨old.gate,RootTables.liveBank H J M fmt.degree rootAt,DepotRAM.Binary.layoutBit fmt M amount second⟩
  winner:=old.winners
  marked:=old.marked
  cable j:=old.signed (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  venues:=old.operands
  source:={
    terrain:=.lit 0
    signed:=fun i=>.lookup (old.signed (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) .row
    owner:=Owners.Board.bank (Owners.Board.venue (DepotRAM.rawBits fmt) M (venuePlan).ownerBase rows) rows
    peers:=old.peers
    cableTables:=DepotRAM.Binary.cables fmt M amount second
    ownerTables:=DepotRAM.Binary.owners fmt M amount second
    ranks:=DonorHeaders.shelf H J M fmt.degree (venuePlan).literal (venuePlan).rankOut
    hubs:=DonorHeaders.shelf H J M fmt.degree (venuePlan).literal (venuePlan).hubOut
    fresh:=DepotRAM.Fresh.Book.bank fmt s K₀ H J M leaf old.topology old.born }

end
end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
