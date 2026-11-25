import OAI.Hierarchy.DescentIssuedPublicDonor
import OAI.Hierarchy.DescentDatedDonorArea
import OAI.Hierarchy.DescentDatedDonorOutputs

namespace OAI
/-! # The actual selected donor and meter lie in the fixed per-date address slice -/
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


theorem public_donor_end :
    ticket.wholeDonorEnd short profile H h base=ticket.donorDate.endAddress h base := rfl

/-- The numerical end of the fixed donor program is exactly the end invoiced
by the ordinary matcher's existing chronological address book. -/
theorem public_donor_span (board seats floor : ℕ) (old : Bank) :
    let a:=ticket.donorDate.schedule h seats board
    ticket.donorDate.endAddress h (a.rotationEnd old floor)≤floor+a.rotationEnd old 0+a.donorWords :=
  ticket.concrete_extent old floor (Nat.clog 2 (S.hostSize i)) board short h amount profile seats


end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
