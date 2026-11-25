import OAI.Hierarchy.DescentCalendarCapturedRoots
import OAI.Hierarchy.DescentCalendarOriginalPeers
import OAI.Hierarchy.DescentCalendarSenderCoordinates
import OAI.Hierarchy.DescentCalendarIssuedMenu

namespace OAI
/-! # Both physical receiver sectors use the original actor, roster, root and donor states -/
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
local notation "pre₀" m => (phys₀).preScalar start₀ oldScene I.sceneFits m
local notation "look₀" => (v₀).jointRegisters base₀ I.earlier
local notation "trunk₀" m => ((phys₀).trunkScene start₀ oldScene I.sceneFits).image m


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
local notation "plate" near => measured_menu B oldBatch batch calendar I cal pad prior₀ xs raw near
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

include frontEq oldEq in
/-- The raw three-neighbor output determines the menu existentially. All source
reads come from the old root book, compact actor prefix and original sender. -/
theorem original_capture (ok : I.Ready)
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
    (joints : shelf*2^Nat.clog 2 ((A).degree+2)≤2^meta₀) :
    ∃found : Fin rawSize→Fin 3→Option (Fin rawSize),
      PhysicalReset.DateInputs.CaptureRoom (plate found) entered ∧
      (∀v : B.next.V,present (selfPeers found) (named₀ v)=(insert v ((Z).emittedNear T v)).map named₀) ∧
      ∀v : B.next.V,(∀j,found (named₀ v) j≠some (named₀ v)) ↔ v∉(Z).emittedNear T v :=by
  obtain ⟨⟨found,rawRows,localMenu,selfMiss⟩,rootRows⟩:=probe
  obtain ⟨low,roots⟩:=capture_catalogue B oldBatch batch calendar paid I cal rc book previous entered
    rootEnd rootRoom pages rootRows
  obtain ⟨registers,three⟩:=capture_registers B oldBatch batch calendar I cal pad prior₀ xs raw found
    floor₀ src before grid oldPos oldBits actor srcFits srcSize chunksWide space oldFits oldSize oldRead rawRows
  have place:=(named_sender_coordinates B oldBatch batch field₀ meta₀ calendar paid (v₀) base₀ old
    frontEq cal.contactDeck I.earlier oldEq).1
  have limit : origEnd<2^bw:=by
    have eqEnd:=congrArg (fun v : CandidateFront=>v.trunkEnd start₀) frontEq
    exact eqEnd ▸ ok.trunk
  have reached:=original_sender_rows B oldBatch batch field₀ meta₀ calendar paid start₀ old
    (dateDir).flags (dateDir).count (dateDir).inverse room₀ donorRoom endRoom pack entered xs raw sender
    limit post area jobs matrix tailRoom earned.keys counter earned.opposite joints
  have contact:=named_sender_reads B oldBatch batch field₀ meta₀ calendar paid (v₀) base₀ old frontEq
    cal.contactDeck I.earlier oldEq I.sceneFits entered (trueContactRegisters B oldBatch batch calendar I pad xs raw)
    (by unfold trueContactRegisters;rw [place];exact reached)
  exact ⟨found,capture_menu B oldBatch batch calendar I cal pad prior₀ xs raw found ok entered oldPos
    low roots contact registers three,localMenu,selfMiss⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
