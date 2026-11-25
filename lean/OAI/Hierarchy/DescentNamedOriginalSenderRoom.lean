import OAI.Hierarchy.DescentCalendarSenderCoordinates

namespace OAI
/-! # Input address bounds for the actual donor census at the reached calendar coordinate -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentPackedZip DescentContactOutputShape DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentDenseHostOrder
open DescentResetPeerUnionRAM DescentPackedColony DescentFallbackPeriod DescentSIMDLookup
open DescentContactDonorFront DescentResetLocalRoster ProtocolRAM
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

variable (paid : input.placement.cap=cap) (v : ResetOutput) (base : ℕ)
    (old : EarlierBanks D k cap n)
local notation "start₀" => v.actorEnd base
local notation "next₀" => (A).oldKeys start₀
local notation "L₀" => peerLayout B next₀ H oldM (A).privateBits ((A).stemField+2) bits
local notation "lo₀" => (L₀).endAddress
local notation "markers₀" => (donor).markers lo₀ shelf bits
local notation "chart" => contactOutputs B H oldM field (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3))
  (S.groupCount (i+1)) (2^k) nextM bits metaBits
local notation "eqShape" => canonical_donor B oldM nextM field metaBits calendar paid
local notation "originals" => calendarOriginals S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR
  calendar start₀ old
variable (front : v.front=(A)) (deck : v.contactShape=chart)

private theorem paid_space {a b : DescentContactDonorFront.Shape} {w lo hi : ℕ}
    (same : a=b) (position : lo=hi) (x : a.Input) (y : b.Input) (sameInputs : HEq x y)
    (room : a.Space lo x w) : b.Space hi y w:=by
  subst b hi
  cases eq_of_heq sameInputs
  exact room

include front deck in
theorem named_sender_room {w : ℕ} (x : v.OriginalOperands base) (source : HEq x originals)
    (room : v.front.SceneRoom start₀ (v.issuedScene base x) w) :
    (donor).Space lo₀ (DescentContactDonorFront.Shape.move eqShape old.donor) w ∧ lo₀<2^w:=by
  obtain ⟨pos,_,origin⟩:=named_sender_coordinates B oldM nextM field metaBits calendar paid v base old front deck x source
  have physical:=(paid_space (congrArg DescentContactOutputShape.Shape.donor deck) pos
    (v.issuedScene base x).donor _ (((cast_heq _ _).symm).trans (heq_of_eq origin)) room.donor)
  obtain ⟨a,b,c⟩:=(donor).ordered lo₀
  exact ⟨physical,(a.trans (b.trans c)).trans_lt ((Nat.le_add_right ..).trans_lt physical.extent)⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
