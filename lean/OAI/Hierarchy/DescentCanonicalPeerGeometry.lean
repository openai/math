import OAI.Hierarchy.DescentCanonicalFrontSources
import OAI.Hierarchy.DescentResetPeerDirectory
import OAI.Hierarchy.DescentResetRankFunctions

namespace OAI
/-! # The selected reset uses the same numerical peer probes as the calendar program -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentSIMDLookup
open DescentResetPeerUnionRAM DescentResetLocalRoster DescentContactDonorFront
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl) (oldM nextM rootField metaBits : ℕ) (calendar : List ℕ)
local notation "A" => CandidateFront.setupFront S ctl.board k tail i D f g oldM nextM rootField metaBits
  C ctl.bitsR calendar
local notation "p₀" => (A).peer
local notation "H" => S.hostSize i
local notation "height" => GroupStage.depthBound D n f g
local notation "cap" => (calendar.take i).prod*256
local notation "cc" => S.groupWidth k tail i
local notation "bits₀" => (p₀).bits
local notation "g₀" => S.groupCount (i+1)
local notation "rawHosts" => H*(DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth) height).card
variable (capDate : input.placement.cap=(calendar.take i).prod*256) (base : ℕ)

theorem canonical_raw_hosts : (p₀).hosts=rawHosts := by rw [B.public_hub_slots];rfl

theorem canonical_peer_layout :
    (A).rawTables base=peerLayout B ((A).oldKeys base) H oldM (A).privateBits ((A).stemField+2) bits₀ := by
  have wires:=same_count B.reset.graph ctl.board B.dimension B.graph height
  change DescentResetCableSlots.cableCap B.reset.graph height=DescentResetCableSlots.cableCap ctl.board height at wires
  unfold peerLayout CandidateFront.rawTables
  rw [B.public_hub_slots,input.branch,B.commonDepth]
  change _=(⟨_,_,_,_,_,_,DescentResetCableSlots.cableCap B.reset.graph height,_,_,_⟩ : RawTables.Layout)
  rw [wires]
  rfl

include capDate in
theorem canonical_donor :
    (A).donor=peerDonorShape B H oldM rootField (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) := by
  unfold peerDonorShape
  rw [input.branch,B.commonDepth,B.keyWidth,B.dimension,capDate]
  simp only [Nat.add_sub_cancel_left]
  rfl

include capDate in
theorem canonical_contact :
    (A).contactLayout base=contactLayout B ((A).donorEnd base) H oldM rootField bits₀ := by
  unfold contactLayout
  rw [B.public_hub_slots,B.commonDepth,B.keyWidth,B.dimension,input.branch,capDate]
  simp only [Nat.add_sub_cancel_left]
  rfl

include capDate in
theorem canonical_probes :
    (p₀).evidence=peerEvidenceRows B ∧ (A).oldKeysCount=stemsCount B ∧
    (A).oldTicketCount=2*DescentFallbackShapeTable.rows (B.reset.k-B.terminals.commonDepth) (2^B.reset.n) := by
  rw [peerEvidenceExact B,capDate]
  refine ⟨rfl,?_,?_⟩
  · unfold stemsCount
    rw [capDate,B.commonDepth,Nat.add_sub_cancel_left]
    rfl
  · rw [B.keyWidth,B.commonDepth,B.dimension,Nat.add_sub_cancel_left]
    rfl

theorem canonical_raw_end :
    (A).rawTablesEnd base=(peerLayout B ((A).oldKeys base) H oldM (A).privateBits ((A).stemField+2) bits₀).endAddress := by
  rw [←canonical_peer_layout B oldM nextM rootField metaBits calendar base]
  exact ((A).tables_end base rfl).symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
