import OAI.Hierarchy.DescentIssuedDonorVisit
import OAI.Hierarchy.DescentPublicDonorPhase

namespace OAI
/-! # Lowering the genuine installed visit to the numerical donor program -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentHostDegree DescentRawCablePanel DescentSIMDLookup DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM DescentPackedZip DescentPackedColony
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
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

def donorDate (_ : OrdinaryLink prior he T c n target) : DonorDate :=
  ⟨k,(A).degree,(A).cap,T.k,T.Δ,(A).z,H,J,G.b,G.C,G.k⟩

theorem issued_public_phase (old : PriorBanks r dim (A).cap K₀) {header factor p : ℕ}
    (oldLow : header≤base) (live : 0<amount) (wide : 2*amount≤h) (size : h≤w)
    (ratio : w≤factor*h) (extent : ticket.wholeDonorEnd short profile H h base≤2^w)
    (grain : T.z=S.grainAt G.b p i) :
    let visit:=ticket.issuedVisit h base old oldLow live wide size ratio extent grain
    (visit.install.seq visit.venue).seq visit.gather=(ticket.donorDate).phase h base w old := by rfl

theorem issued_public_meter (old : PriorBanks r dim (A).cap K₀) {header factor p : ℕ}
    (oldLow : header≤base) (live : 0<amount) (wide : 2*amount≤h) (size : h≤w)
    (ratio : w≤factor*h) (extent : ticket.wholeDonorEnd short profile H h base≤2^w)
    (grain : T.z=S.grainAt G.b p i) :
    let visit:=ticket.issuedVisit h base old oldLow live wide size ratio extent grain
    visit.base=ticket.donorDate.meterBase h base := by rfl

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
