import OAI.Hierarchy.DescentCalendarMixedGeometry
import OAI.Hierarchy.DescentCapturedRankChannels
import OAI.Hierarchy.DescentContactSparseSensors

namespace OAI
/-! # Choosing every channel from the previous physical reset state -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM
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
variable {keyBits : ℕ} (prior : PriorPeerWords B H oldWidth keyBits)
    (xs : Fin H→Fin J→Fin F₀→Cell field₀) (raw : Fin L→Fin K→Fin H→Fin J→Cell field₀)
    (near : Fin rawSize→Fin 3→Option (Fin rawSize))

/-- Four original natural observations are computed by the actual signed donor, halo and mass issuers. -/
def trueContactRegisters (_input : date.DateInputs floor bw) (pad : Fintype.card input.V≤H)
    (xs : Fin H→Fin J→Fin F₀→Cell field₀) (raw : Fin L→Fin K→Fin H→Fin J→Cell field₀) : Fin (good).sockets→Fin 4→Fin (good).sparseHosts→Fin (good).donor.groups→Cell meta₀ :=
  fun q j hostId groupId=>(((good).rawIndicators don₀ (Z).graph xs adj_ raw q).indicators.output j hostId groupId)

private abbrev contactTable (layout : DescentContactOutputShape.Shape) :=
  Fin layout.sockets→Fin 4→Fin layout.sparseHosts→Fin layout.donor.groups→Cell layout.metaBits

def chartPages (_input : date.DateInputs floor bw) (cal : MixedGeometry B oldBatch batch calendar v₀ base₀)
    {keyBits : ℕ} (prior : PriorPeerWords B H oldWidth keyBits) (s : Bool) (t : Root (Q₀).residual (Q₀).ports)
    (hostId : Fin (pitch₀).hosts) (groupId : Fin (pitch₀).groups) : Cell (Q₀).panels :=
  let rEq : (Q₀).residual=r:=congrArg DescentPrivateMaskDeck.Shape.residual cal.privateDeck
  let pEq : (Q₀).ports=2^(Z).n:=congrArg DescentPrivateMaskDeck.Shape.ports cal.privateDeck
  let F : (Q₀).panels=oldWidth*(cap₀*5):=congrArg DescentPrivateMaskDeck.Shape.panels cal.privateDeck
  (prior.privatePages s (cast (congrArg₂ Root rEq pEq) t) (hostId.cast cal.oldHosts) (groupId.cast cal.oldGroups)).cast
    (congrArg (fun b=>2^b) F.symm)

/-- This uses the actual original roster at its old degree. The independently acquired three raw
sockets determine the sorted four-port current list, including self. -/
def measured_menu : I.MeasuredChannels used :=by
  let ns:=fun (h : Fin (peer₀).hosts) (j : Fin 3)=>(near (h.cast cal.peerSlots) j).map (Fin.cast cal.peerSlots.symm)
  refine { rootWords:=chartPages B oldBatch batch calendar I cal prior
           contactValues:=cast (congrArg contactTable cal.contactDeck.symm)
             (trueContactRegisters B oldBatch batch calendar I pad xs raw)
           names:=fun h=>(compactActorName B pad h).cast cal.peerSlots.symm
           now:=indexed (selfPeers ns)
           prior:=fun old j=>(adj_ (old.cast cal.oldCount) (j.cast cal.oldDegree)).map (Fin.cast cal.oldCount.symm)
           near:=ns
           slots:=?_,hosts:=?_,groups:=?_,coarse:=?_,lanes:=?_ }
  · change (peer₀).hosts=(K₀).sparseHosts
    rw [cal.peerSlots,cal.contactDeck]
    rfl
  · rw [cal.privateDeck,cal.oldHosts,cal.palette]; rfl
  · rw [cal.privateDeck,cal.oldGroups]
    exact private_lane_size B
  · rw [cal.contactDeck]
    exact (private_lane_size B).symm
  · rw [cal.privateDeck,cal.oldBatchSize];rfl

/-- Original root, true directory name and raw neighbor record of the concrete constructor. -/
theorem original_menu_words :
    let R:=measured_menu B oldBatch batch calendar I cal pad prior xs raw near
    (∀s t h g,R.rootWords s t h g=chartPages B oldBatch batch calendar I cal prior s t h g) ∧
    (∀h,(R.names h).val=(compactActorName B pad h).val) ∧
    (∀h j,R.near h j=(near (h.cast cal.peerSlots) j).map (Fin.cast cal.peerSlots.symm)):=by
  exact ⟨fun _ _ _ _=>rfl,fun _=>rfl,fun _ _=>rfl⟩

theorem original_contact_words :
    let R:=measured_menu B oldBatch batch calendar I cal pad prior xs raw near
    HEq R.contactValues (trueContactRegisters B oldBatch batch calendar I pad xs raw) :=
  cast_heq (congrArg contactTable cal.contactDeck.symm) _


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
