import OAI.Hierarchy.DescentCalendarCapturedSenders
import OAI.Hierarchy.DescentCalendarSenderRoster

namespace OAI
/-! # The measured sender on the chronological post-trunk memory -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentPackedZip DescentContactOutputShape DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentDenseHostOrder
open DescentResetPeerUnionRAM DescentPackedColony DescentFallbackPeriod DescentSIMDLookup
open DescentContactDonorFront DescentResetLocalRoster ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl) (oldM nextM field metaBits : ℕ) (calendar : List ℕ)
local notation "A" => setupFront S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR calendar
local notation "H" => S.hostSize i
local notation "Ht" => GroupStage.depthBound D n f g
local notation "cap" => (calendar.take i).prod*256
local notation "r" => B.reset.k-B.terminals.commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster B.reset.graph r Ht).card
local notation "bits" => (A).peer.bits
local notation "donor" => peerDonorShape B H oldM field (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3))
variable (paid : input.placement.cap=cap) (floor : ℕ) (old : EarlierBanks D k cap n)
local notation "eqShape" => canonical_donor B oldM nextM field metaBits calendar paid
local notation "U" => (Shape.move eqShape old.donor)
local notation "next" => (A).oldKeys floor
local notation "L" => peerLayout B next H oldM (A).privateBits ((A).stemField+2) bits
local notation "lo" => (L).endAddress
local notation "e" => calendarOriginals S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR
  calendar floor old
variable (flags count inverse : Bank) {w : ℕ}
local notation "scene" => (A).fromOriginals floor e flags count inverse
variable (room : (A).SceneRoom floor scene w)


local notation "markers₀" => (donor).markers lo shelf bits
variable (donorRoom : (donor).Space lo U w)
  (end_ : (markers₀).endAddress<2^w)
  (packed : oldM*max (field*8) bits≤w/2)
local notation "space" => (donor).markerSpace lo shelf bits U donorRoom end_ packed
local notation "early" => RawTables.image B.reset.graph r Ht L (peerTemplate B)
local notation "actual" => (donor).result lo shelf bits U B.reset.graph donorRoom end_ packed

local notation "first₀" => (A).trunkEnd floor
local notation "J₀" => 2^B.terminals.commonDepth
local notation "L₀" => 2^(S.groupWidth k tail i+k-B.terminals.commonDepth)
local notation "K₀" => 2*input.placement.cap
local notation "trueShape" => contactOutputs B H oldM field (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3))
  (S.groupCount (i+1)) (2^k) nextM bits metaBits
local notation "matrix₀" => DescentOldContactSender.count input.placement.degree L₀ input.placement.cap B.reset.n r
local notation "portChart" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "adj_" => DescentPacking.PackedMatch.Local.Stage.hostRotor portChart
  (DescentGroupPeerOrder.hostRoster input.placement ((portChart).trans Fin.valEmbedding))

include donorRoom end_ packed in
/-- The actual memory after the trunk run has all four old signed-donor inputs.
This uses the raw-table memory and donor witness from the same physical peer pass. -/
theorem original_sender_rows (m : Memory w)
    (board : Fin H→Fin J₀→Fin matrix₀→Cell field)
    (words : Fin L₀→Fin K₀→Fin H→Fin J₀→Cell field)
    (before : ((donor).sender lo).Before U board adj_ words (early ((A).probeStart floor scene m)))
    (trunkRoom : first₀<2^w) (post : (markers₀).endAddress≤first₀) (area : (trueShape).endAddress first₀<2^w)
    (jobs : ((donor).sender lo).Packed w) (matrix : oldM*max (field*(markers₀).oldFields) (markers₀).viewBits≤w/2)
    (tailRoom : (trueShape).marker first₀+H*chunks J₀ oldM<2^w)
    (keys : DescentResetLocalRoster.rootSlots r (2^B.reset.n)*(2^B.reset.n+2^Ht)<2^field)
    (counter : oldM*max (field*(L₀*K₀+1)) field≤w/2)
    (opposite : input.placement.degree+2<2^Nat.clog 2 (D+3))
    (joints : shelf*2^Nat.clog 2 (input.placement.degree+2)≤2^metaBits) :
    ∀q j,Source ((trueShape).fieldsAt lo first₀ U q j)
      ((((trueShape).rawIndicators lo B.reset.graph board adj_ words q).indicators.output j)) oldM
      ((trueShape).held lo first₀ U (((A).trunkScene floor scene room).image m)):=by
  refine (trueShape).attained_inputs lo first₀ U B.reset.graph donorRoom post area packed
    board adj_ words (early ((A).probeStart floor scene m)) _ before ?_ jobs matrix tailRoom keys counter opposite joints
  exact reached_contact_trunk_frame B oldM nextM field metaBits calendar paid floor old flags count inverse room
    donorRoom end_ packed m trunkRoom


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
