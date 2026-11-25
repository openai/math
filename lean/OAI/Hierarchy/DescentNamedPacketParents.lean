import OAI.Hierarchy.DescentNamedPacketDirectory
import OAI.Hierarchy.DescentDatedCompactPacketParent
import OAI.Hierarchy.DescentNamedSceneStemRoom

namespace OAI
/-! # Parent packet identifiers read from the selected reset bitmap -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "rawId" => (Z).rawHostRank T rank
local notation "HH" => S.hostSize age
local notation "rows" => (DescentDenseHostOrder.roster (Z).graph ((Z).k-(T).commonDepth) (GroupStage.depthBound D n f g)).card
local notation "dir" => (v).actor.directory actorBase
local notation "prior₀" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "issuedScene₀" => (v).issuedScene base₀ (u).earlier

private theorem flag_bounds (L : DescentResetNewActorDirectory.Layout) {w : ℕ}
    (small : L.endAddress < 2^w) :
    L.flags.Fits w L.endAddress ∧ L.sites ≤ L.flags.size ∧ L.flags.base + L.sites ≤ L.endAddress := by
  obtain ⟨pitch,_,bits,ranks,scratch,values,ending,_⟩ := L.ordered
  have safe := (L.fits small).2.1
  exact ⟨⟨safe.1,safe.2.1,safe.2.2.trans (by omega)⟩,pitch,by omega⟩

/-- The original actor occupancy bits determine every parent packet pointer, including compact padding. -/
theorem DateInputs.fromNamed_packet_parents (degreeAt : venue.degree=D) (blocksAt : venue.k=k)
    (hostsAt : venue.hosts=HH) (capAt : input.placement.cap=cap) (nextLanes : 0<M) (ready : (u).Ready)
    (dst : Memory w) (flags : ∀j : Fin (HH*rows),dst ((dir).flags.base+j.val)=
      if ∃i,rawId i=j then 1 else 0) (positive : 0<HH) :
    DescentResetStemKeyReindex.Directory (H₁:=(v).setup.packets.receivers) (v).setup.packets.parent ((Z).packetOwner T rank positive (pad:=(v).setup.packets.receivers))
      (((v).front.trunkScene early issuedScene₀ (u).sceneFits).image dst) := by
  obtain ⟨_,_,_,numHosts,numShapes,_,population,_⟩:=
    ClosedReset.Window.named_operand_geometry B p drift degree payload e previous M nextM packet
      prior₀ base₀ degreeAt blocksAt hostsAt capAt nextLanes
  have dated := named_successor G S ctl.board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io.wire io.roster floor
  have parentAt : (v).setup.packets.parent = ((v).front.parent early).base := by
    rw [dated]
    rfl
  have paddingAt : (v).setup.packets.receivers = (v).front.newHosts := by
    rw [dated]
    rfl
  have sites : (dir).sites=HH*rows:=by
    change (v).actor.hosts*(v).actor.shapes=_
    rw [dated]
    exact congrArg₂ Nat.mul numHosts numShapes
  have populationAt : (v).front.peer.hosts=HH*rows := by rw [dated]; exact population
  have kinds : (v).front.peer.shapes=rows:=by
    change (DescentDenseHostOrder.roster ctl.board k (GroupStage.depthBound venue.degree n f g)).card=_
    rw [degreeAt]
    exact (DescentExteriorReplay.HopTables.reset_public B).1.symm
  have beforeParent : early≤(v).front.parentStart early:=(v).front.actor_before_parent early rfl
  obtain ⟨flagFit,pitch,flagEnd⟩ := flag_bounds dir ready.actor.room
  rw [parentAt,paddingAt]
  apply (Z).trunk_parent_from_flags T rank positive (v).front early issuedScene₀ (u).sceneFits dst
    B.next.valid.host populationAt kinds
  · exact ⟨flagFit.1,flagFit.2.1,flagFit.2.2.trans beforeParent⟩
  · exact sites ▸ pitch
  · exact sites ▸ flagEnd
  · exact ready.trunk
  · exact flags

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
