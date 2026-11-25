import OAI.Hierarchy.DescentDatedOperandHeaderStep
import OAI.Hierarchy.DescentDatedGatheredHeaderTriplet

namespace OAI
/-! # The original paid prior-header interval contains the old path and rank arrays -/
namespace Hierarchy.DescentDatedSourcePathDirectory
open DescentHaloWalkRAM DescentSIMDLookup DescentDatedAddressBook
open DescentPacking.PackedMatch.Local.Stage.Chooser ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

theorem native_header_room (H G M D first base w : ℕ)
    («over» : PriorHeader.endAddress H G M D first≤base) (packed : base+H<2^w) :
    Fits (nativeBanks H G M D first) H (breadth D) base w ∧
    (PriorHeader.rankBanks H G M D first).endpoints.Fits w base ∧
    (PriorHeader.rankBanks H G M D first).localRank.Fits w base :=by
  let p:=breadth D
  let end_:=PriorHeader.endAddress H G M D first
  have below:base<2^w:=(Nat.le_add_right ..).trans_lt packed
  have head:=«over».trans_lt below
  have fine (j : ℕ) (hj : j<20) : (PriorHeader.bank H G M D first (p+j)).Fits w base:=
    bank_before (PriorHeader.at_bank H G M D first (p+j) (p+20) (Nat.add_lt_add_left hj p) head) «over»
  have room:=PriorHeader.limits H G M D
  exact ⟨⟨fine 15 (by decide),fine 18 (by decide),room.2.2.1,room.2.2.2.1,
    (Nat.le_add_left ..).trans_lt packed,packed⟩,fine 15 (by decide),fine 14 (by decide)⟩

theorem paths_fit_hosts (H G M D base : ℕ) : base+H≤ stop base H G M D :=by
  have positive : 0<breadth D*(D+1):=Nat.mul_pos (by dsimp [breadth];positivity) (Nat.succ_pos _)
  have stride_ : H≤ stride H:=Nat.le_pow_clog (by decide) _
  have room : H≤(breadth D*(D+1))*stride H:=stride_.trans (by simpa only [Nat.one_mul] using
    (Nat.mul_le_mul_right (stride H) (show 1≤breadth D*(D+1) from positive)))
  exact (Nat.add_le_add_left room base).trans (end_le base H G M D)

end
end Hierarchy.DescentDatedSourcePathDirectory

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentDatedSourcePathDirectory DescentPackedZip DescentRawCablePanel
open DescentPacking.PackedMatch.Local.Stage.Chooser DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
variable (floor : ℕ) (A : v.ArgumentEntry)
local notation "e₀" => v.material
local notation "fmt₀" => v.ticket.depotShape v.short
local notation "H₀" => (e₀).oldHosts
local notation "G₀" => (e₀).groups
local notation "M₀" => (e₀).lanes
local notation "D₀" => (fmt₀).degree
local notation "lo₀" => v.originMouthEnd floor
local notation "path₀" => v.operandPathStart floor
local notation "rank₀" => v.operandRankStart floor
local notation "stop₀" => v.operandOldHeaderStart floor

theorem original_header_step {w : ℕ} (m : Memory w) (below : A.venue.panel.base+A.venue.panel.size≤lo₀)
    (rows : H₀*DescentSIMDLookup.chunks (e₀).oldGroups (e₀).oldLanes≤A.venue.panel.size)
    (wide : (e₀).oldLanes*max (DepotRAM.totalBits fmt₀) (e₀).fieldBits≤w/2)
    (earlier : PriorHeader.endAddress H₀ G₀ M₀ D₀ (v.donorEnd floor)≤path₀) (space : stop₀<2^w) :
    Step lo₀ stop₀ (v.operandBeforeHeaders floor w A) m :=by
  have high : rank₀≤ stop₀:=Nat.le_add_right ..
  have span : path₀+H₀≤rank₀:=paths_fit_hosts H₀ G₀ M₀ D₀ path₀
  have low : path₀≤rank₀:=(Nat.le_add_right ..).trans span
  obtain ⟨path,ep,rk⟩:=native_header_room H₀ G₀ M₀ D₀ (v.donorEnd floor) path₀ w earlier (span.trans_lt (high.trans_lt space))
  exact v.before_headers_any floor A m below rows wide path (bank_before ep low) (bank_before rk low) space

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
