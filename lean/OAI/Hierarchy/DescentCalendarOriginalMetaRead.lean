import OAI.Hierarchy.DescentCalendarOriginalCapture
import OAI.Hierarchy.DescentCalendarOriginalHeaders
import OAI.Hierarchy.DescentCalendarStemCoordinates
import OAI.Hierarchy.DescentCalendarEnteredMetaRead

namespace OAI
/-! # Actual paired-sheet metadata from the physical actor and original receiver runs -/
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
set_option hygiene false
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
local notation:max "pre₀" m:arg => (phys₀).preScalar start₀ oldScene I.sceneFits m
local notation "look₀" => (v₀).jointRegisters base₀ I.earlier
local notation:max "trunk₀" m:arg => ((phys₀).trunkScene start₀ oldScene I.sceneFits).image m


variable (floor₀ : ℕ) (src : Bank) (before : Memory bw)
local notation "dir₀" => (⟨floor₀,H,shelf,chunks J oldBatch⟩ : DescentResetNewActorDirectory.Layout)
local notation "entered" => (dir₀).result src before
local notation "ports_" => I.earlier.oldRoster
local notation "name_" => (Z).rawHostRank (T) ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad))

local notation "front₁" => (good).donor
local notation "U₁" => cast (congrArg DescentContactOutputShape.Shape.donorPrior cal.contactDeck) (oldScene).donor
local notation "first₁" => (v₀).trunkEnd base₀
local notation "marks₁" => (front₁).markers don₀ (good).shapes (good).markerBits
local notation "job₁" => (front₁).sender don₀
local notation "count₁" => L*(2*(A).cap)


open DescentFallbackPeriod.Projected DescentResetGates
variable {N keys K₁ R hm l tiny rootWidth senderBits metadata : ℕ}
    (rc : Receiver (A).degree (A).cap N (Z).n r (T).commonDepth H (S.groupCount i) K₁ R oldBatch hm l tiny rootWidth ht bw)
    (book : RootBook (Z).n r (A).degree (2^r) (A).cap rootWidth)
    (previous : PriorPeerWords B H
      (CandidateFront.setupFront S ctl.board k tail i D f g oldBatch batch senderBits metadata C ctl.bitsR calendar).privateBits keys)
local notation "width₀" => calendar_private_width B oldBatch batch senderBits metadata calendar paid
local notation "prior₀" => priorAtWidth B width₀ previous
local notation:max "plate" near:arg => measured_menu B oldBatch batch calendar I cal pad prior₀ xs raw near
local notation "stop₀" => (phys₀).peers start₀
local notation "named₀" => (Z).rawHostRank (T) ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad))

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
local notation "origPrior" => DescentContactDonorFront.Shape.move (canonical_donor B oldBatch batch field₀ meta₀ calendar paid) (old).donor
local notation "origMarks" => (front₁).markers origStart shelf (dateFront).peer.bits
local notation "origJob" => (front₁).sender origStart
local notation "origEnd" => (dateFront).trunkEnd start₀
local notation "origMem" => RawTables.image (Z).graph r ht origL (peerTemplate B) ((dateFront).probeStart start₀ gates entered)

open DescentResetCandidatePair DescentPackedZip DescentResetFieldAssembler
local notation "s₀" => (v₀).sheets
variable (bound : used≤(s₀).hosts) (geo : PhysicalReset.DateInputs.SheetGeometry I)
    (hx : (v₀).receiver.blocks=2^k) (hs : I.sectors.stems=stemsCount B)
    (hc : I.sectors.contacts=contactCount B) (hp : I.sectors.privates=privateCount B)
local notation "pos" => CandidateSheet.index (stemsCount B) (contactCount B) (privateCount B)
local notation "heads" => shaped hx hs hc hp I.sectors.header
local notation "dense₀" => ((Z).denseHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans
    (Fin.castLEEmb pad))).trans (Fin.castLEEmb bound)
local notation "rack₀" => rackOf B dense₀
local notation "meter" => DescentResetFieldAssembler.raw (s₀).metaBits
local notation "fromTrunk" => ((dateFront).trunkScene start₀ gates room₀).image entered

/-- Recover the unmodified three neighbors, including the old self-loop decision,
from the sorted four slots and the observed diagonal bit. -/
theorem raw_menu_from_self {V : Type*} [DecidableEq V] {P : ℕ} (name : V ↪ Fin P)
    (near : Fin P→Fin 3→Option (Fin P)) (hood : V→Finset V)
    (four : ∀v,present (selfPeers near) (name v)=(insert v (hood v)).map name)
    (miss : ∀v,(∀j,near (name v) j≠some (name v)) ↔ v∉hood v) :
    ∀v,present near (name v)=(hood v).map name:=by
  classical
  intro v
  ext z
  by_cases self : z=name v
  · subst z
    have absent : name v∉present near (name v) ↔ v∉hood v:=by
      simpa [present] using miss v
    simpa using not_congr absent
  · have seen:=Finset.ext_iff.mp (four v) z
    rw [self_present,Finset.map_insert] at seen
    simpa [self] using seen

private theorem moveFooterRead {wordSize heightCount groupCount bitsCount chunk : ℕ}
    {leftExpr rightExpr : Expr} {leftEnd rightEnd : ℕ} {leftMem rightMem : Memory wordSize}
    {values : Fin heightCount → Fin groupCount → Cell bitsCount}
    (op : leftExpr = rightExpr) (cutEq : leftEnd = rightEnd) (memEq : leftMem = rightMem)
    (held : rightExpr.Fits wordSize rightEnd ∧ Source rightExpr values chunk rightMem) :
    leftExpr.Fits wordSize leftEnd ∧ Source leftExpr values chunk leftMem := by
  subst rightExpr rightEnd rightMem
  exact held

include geo in
set_option maxHeartbeats 800000 in
/-- The occupied actor directory determines both row order and the original sparse parent.
The earlier stem and trunk programs provide the two native footer projections. -/
theorem original_meta_read (ok : I.Ready)
    (grid : (v₀).actor.directory ((v₀).middle.stop base₀)=dir₀)
    (oldPos : 0<oldBatch) (oldBits : oldBatch≤bw)
    (actor : ∀l (p : Row H J oldBatch),before (src.base+l.val*(H*chunks J oldBatch)+(row H J oldBatch p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B pad) l) p).val:Word bw))
    (srcFits : src.Fits bw floor₀) (srcSize : rawSize*chunks J oldBatch≤ src.size)
    (chunksWide : chunks J oldBatch≤2^bw) (space : (dir₀).endAddress<2^bw)
    (oldFits : (ports_).Fits bw floor₀) (oldSize : H*(A).degree≤(ports_).size)
    (oldRead : ∀a j,before ((ports_).base+(a.val*(A).degree+j.val))=(target (adj_ a j):Word bw))

    (rootEnd : rc.preparedEnd book≤ stop₀) (rootRoom : stop₀<2^bw)
    (pages : ∀s t,I.earlier.pages s t=rc.privatePageBank book s (chartTicket B oldBatch batch calendar cal t))
    (probe : (∃found : Fin rawSize→Fin 3→Option (Fin rawSize),
      (∀h j,(pre₀ entered) (((v₀).initialPeers base₀).base+j.val*rawSize+h.val)=(target (found h j):Word bw)) ∧
      (∀v : B.next.V,present (selfPeers found) (named₀ v)=(insert v ((Z).emittedNear T v)).map named₀) ∧
      ∀v : B.next.V,(∀j,found (named₀ v) j≠some (named₀ v)) ↔ v∉(Z).emittedNear T v) ∧
      ∀s t,Reads (rc.privatePageBank book s t) (previous.privatePages s t) oldBatch (pre₀ entered))
    (donorRoom : (front₁).Space origStart origPrior bw)
    (endRoom : (origMarks).endAddress<2^bw)
    (pack : oldBatch*max (field₀*8) (dateFront).peer.bits≤bw/2)
    (sender : (origJob).Before origPrior xs adj_ raw origMem)
    (post : (origMarks).endAddress≤origEnd) (area : (good).endAddress origEnd<2^bw)
    (jobs : (origJob).Packed bw) (matrix : oldBatch*max (field₀*(origMarks).oldFields) (origMarks).viewBits≤bw/2)
    (tailRoom : (good).marker origEnd+H*chunks J oldBatch<2^bw)
    (counter : oldBatch*max (field₀*(count₁+1)) field₀≤bw/2)
    (earned : ContactFieldRoom B oldBatch batch calendar)
    (joints : shelf*2^Nat.clog 2 ((A).degree+2)≤2^meta₀)
    {p zsize : ℕ} (record : B.Recorded p) (pay : 0<(Z).unit)
    (trees : Bool→(Z).Fallback→DescentPackedFallbackTree.Panel ht zsize)
    (origins : PeerOrigins B pad previous pay trees)
    (sensors : ContactSenderRead B calendar pad xs raw)
    (lanes : 0<I.masked.lanes)
    (rankFit : I.masked.lanes*max (I.masked.field*5) I.masked.field≤bw/2)
    (maskFit : I.masked.lanes*max (I.masked.field*9) (I.masked.field*7)≤bw/2)
    (footer : (∀(x : Fin (2^k)) (j : Fin (stemsCount B)),
      ((dateFront).stemOperand start₀ x.val j.val).Fits bw origEnd ∧
      Source ((dateFront).stemOperand start₀ x.val j.val)
        (fun (h : Fin (s₀).hosts) g=>meter (actualMeta B (originalTrunkRack B) x (stemShelf B j) h g)) (s₀).lanes fromTrunk) ∧
      ∀x : Fin (2^k),((dateFront).trunkOperand start₀ x.val).Fits bw origEnd ∧
      Source ((dateFront).trunkOperand start₀ x.val)
        (fun (h : Fin (s₀).hosts) g=>meter (actualMeta B (originalTrunkRack B) x (trunkCandidate B) h g)) (s₀).lanes fromTrunk) :
    (∃found : Fin rawSize→Fin 3→Option (Fin rawSize),PhysicalReset.DateInputs.CaptureRoom (plate found) entered ∧
      (∀v : B.next.V,present (selfPeers found) (named₀ v)=(insert v ((Z).emittedNear T v)).map named₀) ∧
      ∀v : B.next.V,present found (named₀ v)=((Z).emittedNear T v).map named₀) ∧
    ∀x j,Source (heads x j) (fun h g=>meter (actualMeta B rack₀ x (pos j) h g))
      (s₀).lanes (I.sheetsEntry ok entered):=by
  have reached:=original_capture (B:=B) (oldBatch:=oldBatch) (batch:=batch) (calendar:=calendar)
    (paid:=paid) (I:=I) (cal:=cal) (pad:=pad) (xs:=xs) (raw:=raw)
    (floor₀:=floor₀) (src:=src) (before:=before) (rc:=rc) (book:=book) (previous:=previous)
    (old:=old) (frontEq:=frontEq) (oldEq:=oldEq)
    ok grid oldPos oldBits actor srcFits srcSize chunksWide space oldFits oldSize oldRead rootEnd
    rootRoom pages probe donorRoom endRoom pack sender post area jobs matrix tailRoom counter earned joints
  constructor
  · obtain ⟨found,captured,four,miss⟩:=reached
    exact ⟨found,captured,four,raw_menu_from_self named₀ found ((Z).emittedNear T) four miss⟩
  obtain ⟨_,endEq,stemEq,_,runEq,trunkEq⟩:=original_stem_coordinates frontEq I.earlier dateMenu oldEq
    (dateDir).flags (dateDir).count (dateDir).inverse I.sceneFits room₀
  have sameImage := congrArg (fun phase => phase.image entered) runEq
  apply entered_meta_read B oldBatch batch calendar paid I cal pad prior₀ xs raw bound geo entered
    record pay trees (priorAtWidth_origins B pad width₀ previous pay trees origins)
    hx hs hc hp reached sensors earned ok lanes rankFit maskFit
  · intro x j
    exact moveFooterRead (stemEq x.val j.val) endEq sameImage (footer.1 x j)
  · intro x
    exact moveFooterRead (trunkEq x.val) endEq sameImage (footer.2 x)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
