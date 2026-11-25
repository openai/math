import OAI.Hierarchy.DescentPrivateDonorAllocation
import OAI.Hierarchy.DescentResidentDonorPlacement

namespace OAI
/-! # Original matching suffix through the last ordinary donor register -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentRawCablePanel.DepotRAM DescentRawCablePanel DescentSIMDLookup DescentPacking.PackedMatch.Local DescentHaloWalkRAM
open ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k i z D wire hist : ℕ} {W : MarkedWorld F d P bits}
variable {prior : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
variable {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink prior he T c n target)
namespace OrdinaryLink
variable (short profile H h : ℕ)
local notation "fmt" => ticket.depotShape short
local notation "zfmt" => shape (2^k) prior.placement.degree (2*prior.placement.cap) profile
local notation "sum" => ticket.installedDonorWidth short profile
local notation "lan" => lanes h sum
local notation "rows" => H*chunks (S.groupCount i) lan


local notation "P₀" => breadth prior.placement.degree
local notation "laneSpan" => Resident.Dynamic.Placement.endAddress H (S.groupCount i) lan prior.placement.degree (rawBits fmt) 0
def wholeDonorEnd (oldEnd : ℕ) := ticket.donorEnd short profile H h oldEnd laneSpan

theorem wholeDonorEnd_translate (oldEnd : ℕ) :
    ticket.wholeDonorEnd short profile H h oldEnd=oldEnd+ticket.wholeDonorEnd short profile H h 0 :=
  ticket.donorEnd_translate short profile H h oldEnd laneSpan

theorem ownerCode_fit :
    Owners.inputBits (2^k) prior.placement.degree (2*prior.placement.cap) short ≤ sum := by
  change rawBits fmt≤ sum
  have full : rawBits fmt≤totalBits fmt := by unfold totalBits;omega
  exact full.trans ((le_max_left ..).trans (ticket.installed_donor_widths short profile).1)

theorem wholeDonorEnd_bound (oldEnd : ℕ) :
    ticket.wholeDonorEnd short profile H h oldEnd ≤ oldEnd+
      18*(H*P₀)+26*rows+2*P₀*((lan+1)*(P₀+1))+
      (2*(2*Binary.count fmt+3+2^(k+1))+3)*2^(h/2)+32 := by
  have direct:=ticket.donorEnd_bound short profile H h oldEnd laneSpan
  have dynamic:=Resident.Dynamic.Placement.extent H (S.groupCount i) lan prior.placement.degree (rawBits fmt) 0
  have exponent : rawBits fmt*lan≤h/2 := (Nat.mul_le_mul_right lan (ticket.ownerCode_fit short profile)).trans
    (by simpa [Nat.mul_comm] using lanes_fit h sum)
  have codes : 2^(rawBits fmt*lan)≤2^(h/2) := Nat.pow_le_pow_right (by decide) exponent
  change ticket.donorEnd short profile H h oldEnd laneSpan≤_
  nlinarith only [direct,dynamic,codes]

theorem venue_addresses (oldEnd : ℕ) :
    let root:=ticket.donorStart short profile H h oldEnd
    let source:=ticket.donorSource short profile H h oldEnd laneSpan
    source.base=Resident.Dynamic.Placement.endAddress H (S.groupCount i) lan prior.placement.degree (rawBits fmt) root ∧
      source.base+source.size=ticket.donorMeter short profile H h oldEnd laneSpan := by
  exact ⟨(Resident.Dynamic.Placement.translate ..).symm,rfl⟩

end OrdinaryLink
end
end Hierarchy.DescentSixParty.Chronology

end OAI
