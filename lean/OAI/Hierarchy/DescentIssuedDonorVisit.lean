import OAI.Hierarchy.DescentDonorPublicBanks
import OAI.Hierarchy.DescentPrivateDonorDiary
import OAI.Hierarchy.DescentDepotResidentRoom
import OAI.Hierarchy.DescentPrivateInstalledAny

namespace OAI
/-! # Concrete donor date from the selected physical packet and its prior banks -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentHostDegree DescentRawCablePanel DescentSIMDLookup DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM DescentPackedZip DescentPackedColony
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
local notation "r" => 2^k
local notation "cm" => 2*(A).cap
local notation "K₀" => 2^(k+1)
local notation "dim" => (A).degree
local notation "short" => max (k+3) (Nat.clog 2 (dim+1))
local notation "profile" => DescentTerminalEpochBits.width G.C
local notation "fmt" => ticket.depotShape short
local notation "s" => shape r dim cm profile
local notation "amount" => ticket.installedDonorWidth short profile
variable (h base : ℕ)
local notation "M" => lanes h amount
local notation "rows" => H*chunks J M
local notation "rootAt" => ticket.donorStart short profile H h base
local notation "span₀" => DepotRAM.Resident.Dynamic.Placement.endAddress H J M dim (DepotRAM.rawBits fmt) 0
local notation "src" => ticket.donorSource short profile H h base span₀
local notation "meter" => ticket.donorMeter short profile H h base span₀
local notation "second" => base+DescentSIMDLookup.Book.words (DepotRAM.totalBits fmt) H J M
local notation "leaf" => second+DepotRAM.Binary.count fmt*(2*2^(amount*M))
local notation "band" => DepotRAM.Resident.Dynamic.Placement.layout H J M dim (DepotRAM.rawBits fmt) rootAt
local notation "books" => DepotRAM.Binary.joints fmt M amount second

variable (old : PriorBanks (2^k) prior.placement.degree prior.placement.cap (2^(k+1)))
local notation "layout" => band old.peers.roster old.hub
local notation "top" => old.topology
local notation "born" => old.born

def issuedAddressed : DepotRAM.Resident.Addressed fmt K₀ :=
  publicAddressed fmt s K₀ H J M amount rootAt second leaf old

local notation "address" => issuedAddressed ticket h base old
local notation "ptr" => DepotRAM.Resident.addressed fmt address H
local notation "rom" => DescentSIMDLookup.Book.banks base (DepotRAM.totalBits fmt) H J M src
local notation "pad" => prior.valid.host.trans (DescentCompiler.TerminalScale.hostPad _)

def issuedVisit {header factor p : ℕ} (oldLow : header≤base)
    (live : 0<amount) (wide : 2*amount≤h) (size : h≤w) (ratio : w≤factor*h)
    (extent : ticket.wholeDonorEnd short profile H h base≤2^w) (grain : T.z=S.grainAt G.b p i) :
    DonorVisit ticket header h w factor p where
  base:=meter
  setupBase:=base
  priorHub:=old.hub
  tables:=books
  addresses:=address
  banks:=rom
  live:=live
  wide:=wide
  fits:=ticket.donor_fits short profile H h base span₀ pad oldLow wide size ratio extent
  quantum:=grain

theorem source_tree : DepotRAM.Setup.sources fmt s K₀ H J M amount base ptr top born=ptr := rfl

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
