import OAI.Hierarchy.DescentNamedResetOutput
import OAI.Hierarchy.DescentPhysicalMixedCapture
import OAI.Hierarchy.DescentPrivatePanelProjection
import OAI.Hierarchy.DescentCalendarPrivatePages
import OAI.Hierarchy.DescentContactSelectedJoint

namespace OAI
/-! # Numerical identification of every source dimension on the actual dated reset menu -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open ProtocolRAM
open scoped Classical
noncomputable section
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "H" => S.hostSize i
local notation "J" => 2^(T).commonDepth
local notation "r" => (Z).k-(T).commonDepth
local notation "ht" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r ht).card
local notation "gs" => S.groupCount (i+1)
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(ht+1))
local notation "oldWidth" => DescentPackedPrivateMenu.fieldBits (Z).graph r ht (2^r*(2*(A).cap))
    (DescentRecordedRotorLayers.width f (A).cap) C (Z).width
variable (oldBatch batch : ℕ) (calendar : List ℕ) (paid : (A).cap=(calendar.take i).prod*256)
local notation "cap" => (calendar.take i).prod*256
local notation "field₀" => ResetMiddle.fieldWidth D cap n k ht
local notation "table₀" => CandidateSheets.fromBoard S ctl.board k tail i D f g cap batch
local notation "meta₀" => (table₀).metaBits
local notation "month" => CandidateFront.menu S ctl.board k tail i D f g oldBatch batch C ctl.bitsR calendar
local notation "good" => contactOutputs B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) gs (2^k)
    batch (month).contact.outputBits meta₀
local notation "deck" => privateProjection («H»:=H) (field:=oldWidth) B oldBatch batch meta₀
variable (v : ResetOutput) (front : v.front=month) (sheets : v.sheets=table₀) (base : ℕ)
local notation "p" => v.front.peer
local notation "C₀" => v.front.contactLayout (v.actorEnd base)
local notation "Q" => v.privateShape
local notation "K" => v.contactShape

structure MixedGeometry (v : ResetOutput) (base : ℕ) : Prop where
  privateDeck : v.privateShape=deck
  contactDeck : v.contactShape=good
  oldHosts : (v.front.contactLayout (v.actorEnd base)).hosts=H
  oldGroups : (v.front.contactLayout (v.actorEnd base)).groups=J
  palette : (v.front.contactLayout (v.actorEnd base)).shapes=shelf
  peerSlots : v.front.peer.hosts=H*shelf
  oldDegree : v.front.peer.oldDegree=(A).degree
  oldCount : v.front.peer.oldHosts=H
  peerShapes : v.front.peer.shapes=shelf
  currentCount : v.sheets.hosts=S.hostSize (i+1)
  oldBatchSize : (v.front.contactLayout (v.actorEnd base)).batch=oldBatch
  fieldWidth : v.sheets.metaBits=CandidateFront.endpointWidth D shelf (2^g*cap)

include paid front sheets in
theorem mixed_geometry : MixedGeometry B oldBatch batch calendar v base :=by
  have hb : (month).peer.shapes=shelf:=B.public_hub_slots.symm
  have rb : r=k:=calendar_residual B
  have field : (month).privateBits=oldWidth:=
    calendar_private_width B oldBatch batch field₀ meta₀ calendar paid
  have wire:=same_count (Z).graph ctl.board B.dimension B.graph ht
  change cap₀=DescentResetCableSlots.cableCap ctl.board ht at wire
  have dnr : (month).donor=donorFront B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)):=
    canonical_donor B oldBatch batch field₀ meta₀ calendar paid
  constructor
  · unfold ResetOutput.privateShape privateProjection
    rw [front,sheets,hb,field]
    change DescentPrivateMaskDeck.Shape.mk _ _ _ _ _ _ (DescentResetCableSlots.cableCap ctl.board ht) _ _ k (2^n)=_
    rw [←wire,rb]
    congr 1
    exact congrArg (fun x : ℕ => 2^x) B.dimension.symm
  · unfold ResetOutput.contactShape contactOutputs
    rw [front,sheets,dnr,hb]
    rfl
  · rw [front];rfl
  · rw [front,B.commonDepth];rfl
  · rw [front];exact hb
  · rw [front];exact canonical_raw_hosts B oldBatch batch field₀ meta₀ calendar
  · rw [front,input.branch];rfl
  · rw [front];rfl
  · rw [front];exact hb
  · rw [sheets];rfl
  · rw [front];rfl
  · rw [sheets,B.public_hub_slots];rfl

/-- The dated allocator uses this same numerical front and sheet. -/
theorem fromBoard_menu (p₀ drift degree payload e previous nextM base : ℕ)
    (old : ResetOutput.Prior) (priorDegree : old.venue.degree=D) :
    let date:=ResetOutput.fromBoard G S ctl.board k tail i p₀ f g drift degree payload e previous batch
      nextM C ctl.bitsR old base
    let fees:=DescentCompiler.capCalendar G.b S.rounds g S.height
    date.front=CandidateFront.menu S ctl.board k tail i D f g (2^e) batch C ctl.bitsR fees ∧
      date.sheets=CandidateSheets.fromBoard S ctl.board k tail i D f g ((fees.take i).prod*256) batch :=by
  unfold ResetOutput.fromBoard
  rw [priorDegree]
  exact ⟨rfl,rfl⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
