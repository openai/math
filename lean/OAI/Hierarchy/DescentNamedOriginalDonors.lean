import OAI.Hierarchy.DescentNamedDonorWiring
import OAI.Hierarchy.DescentNamedWordReturn
import OAI.Hierarchy.DescentReachedOriginalNumericFields

namespace OAI
/-! The real three-column native donor receipt on the final, compact original-number rack. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetNewActorDirectory DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
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
local notation "pre₀" m:arg => (phys₀).preScalar start₀ oldScene I.sceneFits m
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


open DescentPackedZip DescentResetOriginalDonors
local notation "sx" => (v₀).sheets
local notation "sel" => (sx).selectorBits
local notation "short" => (sx).shortBits
local notation "nd" => (v₀).originalDonorLayout I.numbered.signedSlots
local notation "fromNum" => (good).numberingLayout sel short
local notation "name₀" => originalCompactName B H pad
local notation "groupAt" => congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck
local notation "blockAt" => congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck
local notation "index_" => (Z).denseHostRank (T) (B.frame.host.symm.toEmbedding.trans portChart)
local notation "actualName" => fun t : Fin used=>(name₀ t).cast cal.peerSlots.symm

private theorem val_cast_comp {a₁ b₁ c₁ : DescentResetOriginalDonors.Layout} (p : a₁=b₁) (q : b₁=c₁) (y : c₁.Values) :
    cast (congrArg DescentResetOriginalDonors.Layout.Values p.symm) (cast (congrArg DescentResetOriginalDonors.Layout.Values q.symm) y)=
    cast (congrArg DescentResetOriginalDonors.Layout.Values (p.trans q).symm) y:=by
  cases p;cases q;rfl

set_option maxHeartbeats 850000 in
include frontEq oldEq in
/-- Both the RAM address and the name resolved on an occupied row come from this
single earlier signed transaction. Ghost rows keep the publisher's zero extension. -/
noncomputable def named_original_donors (ok : I.Ready) (m : Memory bw)
    (wiring : I.DonorWiring) (registered : NumberGeometry B I) (bound : used≤(sx).hosts)
    (donorRoom : (front₁).Space origStart origPrior bw)
    (endRoom : (origMarks).endAddress<2^bw) (pack : oldBatch*max (field₀*8) (dateFront).peer.bits≤bw/2)
    (sender : (origJob).Before origPrior xs adj_ raw (origMem m))
    (post : (origMarks).endAddress≤origEnd) (jobs : (origJob).Packed bw)
    (matrix : oldBatch*max (field₀*(origMarks).oldFields) (origMarks).viewBits≤bw/2)
    (tailRoom : (good).marker origEnd+H*chunks J oldBatch<2^bw)
    (earned : ContactFieldRoom B oldBatch batch calendar)
    (counter : oldBatch*max (field₀*(count₁+1)) field₀≤bw/2)
    (eqn : J=gs*(2^k))
    (real : ContactSenderRead B calendar pad xs raw)
    (labelFit : originalChoices B<2^sel) (shortFit : max (originalChoices B) ((A).degree+2)<2^short)
    (metaFit : (A).degree+2<2^meta₀)
    (count : m (dateDir).count.base=(used:Word bw))
    (inverse : ∀j:Fin used,m ((dateDir).inverse.base+j.val)=((name₀ j).val:Word bw))
    (countFits : used<2^bw) (hostsFit : (sx).hosts≤2^bw) (invSize : used≤(dateDir).inverse.size) :
    WordDonors B oldBatch batch calendar I cal pad bound registered m:=by
  let values₀:=donorVals sel short eqn
  let q := congrArg (fun z : DescentContactOutputShape.Shape=>z.numberingLayout sel short) cal.contactDeck
  let alignment := wiring.projected.trans q
  let vᵣ:=(cast (congrArg DescentResetOriginalDonors.Layout.Values alignment.symm) values₀ : (nd).Values)
  let nm (ord : Fin used):Fin (nd).sparseHosts := (name₀ ord).cast (congrArg (·.sparseHosts) alignment).symm
  have seen:=calendar_original_donor_seen B oldBatch batch calendar paid I cal pad xs raw old frontEq oldEq ok m
    donorRoom endRoom pack sender post jobs matrix tailRoom earned counter sel short eqn
  have got:=I.donor_fields_of_seen wiring ok m nm _ seen count inverse countFits hostsFit invSize
  let kept := cast (congrArg DescentResetOriginalDonors.Layout.Values wiring.projected.symm)
    (cast (congrArg DescentResetOriginalDonors.Layout.Values q.symm) values₀)
  have same : kept = vᵣ := val_cast_comp wiring.projected q values₀
  refine ⟨(fun x side j=>(nd).denseLabel nm kept (x.cast (blockAt).symm) side j),
    (fun x side f j=>(nd).denseCargo nm kept (x.cast (blockAt).symm) side f j),?_,?_,?_⟩
  · intro x side j
    exact got.1 (x.cast (blockAt).symm) side j
  · intro x side flag j
    exact got.2 (x.cast (blockAt).symm) side flag j
  intro x v t occupied gr
  rw [same]
  obtain ⟨setup,measured⟩:=real.original
  have ports (v : input.V) (j : Fin (A).degree) :
      adj_ (portChart v) j=(hostRoster (A) (input.vertex.trans Fin.valEmbedding) v j).map portChart:=by
    have hit : ∃u,portChart u=portChart v:=⟨v,rfl⟩
    rw [hostRotor,dite_eq_left hit,(portChart).injective hit.choose_spec]
    rfl
  have pos : 0<field₀:=by unfold ResetMiddle.fieldWidth;omega
  have actual:=occupied_numbered_fields B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) origStart
    (month).contact.outputBits pad xs adj_ raw setup measured ports real.signed earned.signed pos batch meta₀
    earned.port earned.opposite sel short eqn labelFit shortFit metaFit bound v t occupied (gr.cast groupAt) x
  refine ⟨?_,?_,?_⟩
  · intro side j
    exact (DescentResetOriginalDonors.Layout.denseLabel_transport alignment name₀ values₀ _ side _ v gr).trans (actual.1 side j)
  · intro side j e he
    exact (DescentResetOriginalDonors.Layout.denseCargo_transport alignment name₀ values₀ _ side 0 _ v gr).trans (actual.2.1 side j e he)
  · intro side j e he
    exact (DescentResetOriginalDonors.Layout.denseCargo_transport alignment name₀ values₀ _ side 1 _ v gr).trans (actual.2.2 side j e he)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
