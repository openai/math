import OAI.Hierarchy.DescentPublicDonorAny
import OAI.Hierarchy.DescentIssuedDonorReadRoom
import OAI.Hierarchy.DescentIssuedPublicDonor

namespace OAI
/-! # The authenticated static predecessor layout supplies every arbitrary-input donor bound -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentRawCablePanel DescentPackedZip DescentSIMDLookup DescentPacking.PackedMatch.Local
open DescentPackedColony DescentHostDegree ProtocolRAM Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε u : ℝ} {k i z D wire hist w : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he T c n target)
local notation "A" => prior.placement
local notation "H" => DescentCompiler.TerminalScale.hostRows (S.hostSize i)
local notation "J" => S.groupCount i
local notation "K" => 2^(k+1)
local notation "r" => 2^k
local notation "cm" => 2*(A).cap
local notation "D₀" => (A).degree
local notation "short" => max (k+3) (Nat.clog 2 (D₀+1))
local notation "prof" => DescentTerminalEpochBits.width G.C
local notation "fmt" => ticket.depotShape short
local notation "s" => shape r D₀ cm prof
local notation "amount" => ticket.installedDonorWidth short prof
variable (h base : ℕ) (old : PriorBanks (2^k) prior.placement.degree prior.placement.cap (2^(k+1)))
local notation "M" => lanes h amount
local notation "rows" => H*chunks J M
local notation "N" => (K*H)*chunks J M
local notation "rootAt" => ticket.donorStart short prof H h base
local notation "span₀" => DepotRAM.Resident.Dynamic.Placement.endAddress H J M D₀ (DepotRAM.rawBits fmt) 0
local notation "src" => ticket.donorSource short prof H h base span₀
local notation "address" => issuedAddressed ticket h base old
local notation "inputs" => DepotRAM.Resident.addressed fmt address H
local notation "postgeom" => DepotRAM.Resident.Dynamic.Placement.layout H J M D₀ (DepotRAM.rawBits fmt) rootAt old.peers.roster old.hub

private theorem bound_slices {base size source width stop count limit : ℕ}
    (before : base + 2 * (size+1) ≤ source) (after_ : source+width ≤ stop+1)
    (finish : stop+1+count < limit) : source < limit ∧ base+size < limit := by omega

set_option maxHeartbeats 800000 in
theorem public_phase_room (ok : ReadRoom ticket h base old w)
    (extent : ticket.wholeDonorEnd short prof H h base≤2^w) :
    ticket.donorDate.PhaseRoom h base w old := by
  let size:=ticket.setupWords short prof H h
  let end₀:=ticket.donorMeter short prof H h base span₀
  have parts:=DonorSpace.leaves base size span₀ rows h
  have finish : end₀+1+rows<2^w := parts.2.2.2.trans_le extent
  have before : base+2*(size+1)≤ (src).base := parts.2.1
  have after : (src).base+(src).size≤end₀+1 := parts.2.2.1
  have bounds := bound_slices before after finish
  have budget := bounds.1
  have price:=(ticket.installed_donor_widths short prof).2.2
  have gather:=DepotRAM.Setup.room fmt s K H J M amount base (src).base inputs old.topology old.born
    price before budget ok.signed ok.terrain ok.peers ok.ranks ok.hubs ok.sourceTopology ok.sourceBirths
    ok.topRows ok.birthRows ok.birthWidth
  have table:=DepotRAM.Setup.lookup_room fmt s K H J M amount base src before parts.1 after finish ok.packed
  exact ⟨bounds.2,ok.geometry,gather.2,table.1⟩

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
