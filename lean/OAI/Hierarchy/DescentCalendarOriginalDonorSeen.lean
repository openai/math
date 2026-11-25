import OAI.Hierarchy.DescentCalendarSenderCoordinates
import OAI.Hierarchy.DescentPhysicalOriginalDonorFrame
import OAI.Hierarchy.DescentResetOriginalDonorMemory
import OAI.Hierarchy.DescentCalendarStemCoordinates

namespace OAI
/-! The actual dated previous sender as the input to the original-number publisher. -/
namespace Hierarchy.DescentContactOutputShape.Shape
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable def originalValues (s : Shape) (sel short : ℕ) := (s.numberingLayout sel short).Values

theorem original_seen_transport {A B : Shape} (eqn : A=B) (lo first sel short : ℕ) (src : A.donorPrior)
    (val : B.originalValues sel short) {w : ℕ} (m : Memory w)
    (seen : (B.numberingLayout sel short).Seen (B.originalSensors lo first (cast (congrArg donorPrior eqn) src)) val m) :
    (A.numberingLayout sel short).Seen (A.originalSensors lo first src)
      (cast (congrArg (fun n : Shape=>n.originalValues sel short) eqn.symm) val) m:=by
  subst B
  exact seen

theorem held_transport {A B : Shape} (same : A=B) (lo first : ℕ) (src : A.donorPrior) {w : ℕ} (m : Memory w) :
    A.held lo first src m=B.held lo first (cast (congrArg donorPrior same) src) m:=by
  subst B
  rfl
end Hierarchy.DescentContactOutputShape.Shape

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetNewActorDirectory DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
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
variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "phys₀" => (v₀).front
local notation "peer₀" => (phys₀).peer
local notation "pitch₀" => (phys₀).contactLayout ((v₀).actorEnd base₀)
local notation "Q₀" => (v₀).privateShape
local notation "K₀" => (v₀).contactShape
local notation "don₀" => (phys₀).donorStart ((v₀).actorEnd base₀)
local notation "used" => Fintype.card B.next.V
local notation "rawSize" => H*shelf
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "F₀" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
variable (cal : MixedGeometry B oldBatch batch calendar v₀ base₀) (pad : Fintype.card input.V≤H)
local notation "portChart" => input.vertex.trans (Fin.castLEEmb pad)
local notation "adj_" => hostRotor portChart (hostRoster (A) ((portChart).trans Fin.valEmbedding))
variable (xs : Fin H→Fin J→Fin F₀→Cell field₀) (raw : Fin L→Fin K→Fin H→Fin J→Cell field₀)



local notation "oldScene" => (v₀).issuedScene base₀ I.earlier
local notation "start₀" => (v₀).actorEnd base₀
local notation "pre₀" m => (phys₀).preScalar start₀ oldScene I.sceneFits m
local notation "look₀" => (v₀).jointRegisters base₀ I.earlier
local notation "trunk₀" m:arg => ((phys₀).trunkScene start₀ oldScene I.sceneFits).image m


open CandidateFront
local notation "dateFront" => setupFront S ctl.board k tail i D f g oldBatch batch field₀ meta₀ C ctl.bitsR calendar
variable (old : EarlierBanks D k cap n)
local notation "dateMenu" => calendarOriginals S ctl.board k tail i D f g oldBatch batch field₀ meta₀ C ctl.bitsR calendar start₀ old
variable (frontEq : (phys₀)=dateFront) (oldEq : HEq I.earlier dateMenu)
local notation "dateDir" => (v₀).actor.directory ((v₀).middle.stop base₀)
local notation "gates" => (dateFront).fromOriginals start₀ dateMenu (dateDir).flags (dateDir).count (dateDir).inverse
local notation "room₀" => original_room frontEq I.earlier dateMenu oldEq (dateDir).flags (dateDir).count (dateDir).inverse I.sceneFits
local notation "origL" => peerLayout B ((dateFront).oldKeys start₀) H oldBatch (dateFront).privateBits
  ((dateFront).stemField+2) (dateFront).peer.bits
local notation "origStart" => (origL).endAddress
local notation "origPrior" => DescentContactDonorFront.Shape.move (canonical_donor B oldBatch batch field₀ meta₀ calendar paid) old.donor
local notation "front₁" => (good).donor
local notation "origMarks" => (front₁).markers origStart shelf (dateFront).peer.bits
local notation "origJob" => (front₁).sender origStart
local notation "origEnd" => (dateFront).trunkEnd start₀
local notation "origMem" entered:arg => RawTables.image (Z).graph r ht origL (peerTemplate B) ((dateFront).probeStart start₀ gates entered)



local notation "first₁" => (v₀).trunkEnd base₀
local notation "fromTrunk" m:arg => ((dateFront).trunkScene start₀ gates room₀).image m
local notation "count₁" => L*K
local notation "donorVals" sel:arg short:arg eqn:arg => (good).numberingValues origStart (Z).graph xs adj_ raw sel short eqn

include frontEq oldEq in
/-- The sender read is exactly the old-sender component of `calendar_original_probe`.
The trunk and every later phase up through the donor-deck entry are followed in the same RAM. -/
theorem calendar_original_donor_seen (ok : I.Ready) (m : Memory bw)
    (donorRoom : (front₁).Space origStart origPrior bw)
    (endRoom : (origMarks).endAddress<2^bw) (pack : oldBatch*max (field₀*8) (dateFront).peer.bits≤bw/2)
    (sender : (origJob).Before origPrior xs adj_ raw (origMem m))
    (post : (origMarks).endAddress≤origEnd) (jobs : (origJob).Packed bw)
    (matrix : oldBatch*max (field₀*(origMarks).oldFields) (origMarks).viewBits≤bw/2)
    (tailRoom : (good).marker origEnd+H*chunks J oldBatch<2^bw)
    (earned : ContactFieldRoom B oldBatch batch calendar)
    (counter : oldBatch*max (field₀*(count₁+1)) field₀≤bw/2)
    (sel short : ℕ) (eqn : J=gs*(2^k)) :
    ((K₀).numberingLayout sel short).Seen ((K₀).originalSensors don₀ first₁ (oldScene).donor)
      (cast (congrArg (fun X : DescentContactOutputShape.Shape=>X.originalValues sel short) cal.contactDeck.symm)
        (donorVals sel short eqn)) (I.donorDeckEntry m) :=by
  obtain ⟨place,_,operand⟩:=named_sender_coordinates B oldBatch batch field₀ meta₀ calendar paid
    (v₀) base₀ old frontEq cal.contactDeck I.earlier oldEq
  have roof : first₁=origEnd:=congrArg (fun a : CandidateFront=>a.trunkEnd start₀) frontEq
  have limit : origEnd<2^bw:=roof ▸ ok.trunk
  have trunkEq:=(original_stem_coordinates frontEq I.earlier dateMenu oldEq (dateDir).flags (dateDir).count
    (dateDir).inverse I.sceneFits room₀).2.2.2.2.1
  have trunk : trunk₀ m=fromTrunk m:=congrArg (fun phase=>phase.image m) trunkEq
  have kept:=reached_contact_trunk_frame B oldBatch batch field₀ meta₀ calendar paid start₀ old
    (dateDir).flags (dateDir).count (dateDir).inverse room₀ donorRoom endRoom pack m limit
  have key : (K₀).choicePage first₁=(good).choicePage origEnd:=by rw [cal.contactDeck,roof]
  have frame (p : ℕ) (hp : p<(good).choicePage origEnd) :
      I.donorDeckEntry m p=(good).held origStart origEnd origPrior (fromTrunk m) p:=by
    have take:=I.original_donor_frame m ok p (key.symm ▸ hp)
    change I.donorDeckEntry m p=(K₀).held don₀ first₁ (oldScene).donor (trunk₀ m) p at take
    have moved := take.trans (congrFun (DescentContactOutputShape.Shape.held_transport
      cal.contactDeck don₀ first₁ (oldScene).donor (trunk₀ m)) p)
    rw [place,roof] at moved
    exact moved.trans (congrArg₂ (fun (u : (good).donorPrior) (mem : Memory bw) =>
      (good).held origStart origEnd u mem p) operand trunk)
  have area:(good).endAddress origEnd<2^bw:=by
    have extentBound : (K₀).endAddress first₁<2^bw:=ok.mass
    rwa [cal.contactDeck,roof] at extentBound
  have seen:=(good).numbered_reads origStart origEnd origPrior (Z).graph donorRoom endRoom pack xs adj_ raw
    (origMem m) (fromTrunk m) sender jobs matrix post tailRoom earned.keys counter earned.opposite kept
    (((good).cuts origEnd).2.2.2.2.2.trans_lt area) sel short eqn (I.donorDeckEntry m) frame
  apply DescentContactOutputShape.Shape.original_seen_transport cal.contactDeck
  rw [place,roof]
  exact (congrArg (fun (u : (good).donorPrior) =>
    ((good).numberingLayout sel short).Seen ((good).originalSensors origStart origEnd u)
      (donorVals sel short eqn) (I.donorDeckEntry m)) operand).mpr seen

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
