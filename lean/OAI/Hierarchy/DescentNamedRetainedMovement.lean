import OAI.Hierarchy.DescentDatedRetainedRootFrame
import OAI.Hierarchy.DescentNamedVenueActorDirectory
import OAI.Hierarchy.DescentNamedCapturedActorBounds
import OAI.Hierarchy.DescentNamedCalendarRootPacket
import OAI.Hierarchy.DescentPhysicalResetActorOutput

namespace OAI
/-! The two physically moved panels use the compact directory order of the selected reset. -/
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
local notation "nextCPU" => (a).successor
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
local notation "actorBase" => (nextCPU).middle.stop base₀
local notation "early" => (nextCPU).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (nextCPU).front.SceneRoom early ((nextCPU).issuedScene base₀ older) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "rawId" => (Z).rawHostRank T rank
local notation "HH" => S.hostSize age
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage
local notation "priorCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal io.wire io.roster nextCPU
local notation "sourceRows" => DescentResetCanvasIngress.datedLayout input HH (nextCPU).funded.oldLanes
  (priorCPU).lanes (priorCPU).short (nextCPU).funded.precision (priorCPU).bits
local notation "oldCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal
  ((sourceRows).tokenAt floor) io.roster nextCPU
local notation "geom₀" => (a).chart start
local notation "fresh" => (geom₀).remixEnd (a).payload (a).gain (a).positive
local notation "phys₀" => DescentGLPacked.BankImage.Dated.chart (E).endAddress (geom₀).routedHosts (a).high (a).low (a).bits
local notation "saved" => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim
local notation "chip" => ((phys₀).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length
local notation "digits" => S.resetInputDigits ctl.base ctl.radix age
local notation "peer₀" => PackedFlow.portAt input.placement (input.placement.numberedHeader digits input.vertex).site

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (DescentDenseHostOrder.roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "prev" => fun v=>(Z).placement.b (B.frame.host v)
local notation "U" => (nextCPU).actor
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (u).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (u).actor actorBase w)+(dir).ticks scene

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

local notation "setup" => (nextCPU).setup
local notation "r" => (setup).retained
local notation "oldBank" => (u).bank
local notation "at_" => (nextCPU).operandFloor base₀
local notation "src" => (r).Values
local notation "Sigs" => Fin (setup).strip→Fin (setup).placement.oldHosts→Fin ((setup).placement.groups*(setup).placement.blocks)→Cell (setup).signedBits
local notation "N" => Fintype.card B.next.V
local notation "width" => (E).dim
open DescentSixParty.PackedFlow.Channels

private theorem native_dimension {a₀ d₀ : ℕ} (h : a₀=d₀) (L : DescentGL.Layout a₀) :
    (DescentExterior.matrixCode (cast (congrArg DescentGL.Layout h) L)).val=(DescentExterior.matrixCode L).val :=by cases h;rfl

theorem DateInputs.fromNamed_retained_moved (ready : (u).Ready) (degreeAt : venue.degree=D)
    (capAt : input.placement.cap=cap) (blocksAt : venue.k=k) (oldH : venue.hosts=HH)
    (positive : 0<M) (priorPos : 0<oldLanes) (newFit : S.hostSize (age+1)≤2^w)
    (μ : DescentGL.Layout width) (mem measured mid : Memory w) (old : src) (X₀ : (setup).seven.Packets) (signals : Sigs)
    (banks : ∀i,((oldBank).old i).Fits w floor ∧ (r).hosts*chunks (r).groups (r).previousLanes≤((oldBank).old i).size ∧
      Reads ((oldBank).old i) (old i) (r).previousLanes mem)
    (savedWord : measured (P).saved=((DescentExterior.matrixCode μ).val:Word w)) (prefixFrame : ∀j,j<floor→measured j=mem j)
    (scanned : ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
      (S.groupCount age) venue.degree w).Exec ((entry₀).image mem) measured
      ((a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w))
    (publication : (pub).Exec measured ((dir).result scene mid) ticks)
    (countWord : (dir).result scene mid (dir).count.base=(N:Word w))
    (inverseWord : ∀v₀ : B.next.V,(dir).result scene mid ((dir).inverse.base+((Z).denseHostRank T rank v₀).val)=((rawId v₀).val:Word w))
    (outerFrame : ∀j,j<(rc).origin ∨ (dir).endAddress≤j→(dir).result scene mid j=measured j)
    (innerFrame : ∀i,i<actorBase→mid i=(rc).preparedImage book prepared measured i)
    (window : Source (oldBank).window X₀ (setup).seven.packetLanes ((rc).preparedImage book prepared measured))
    (signed : ∀j,Source ((oldBank).signed j) (signals j) (setup).signedLanes ((rc).preparedImage book prepared measured)) :
    ∃(geo : (setup).MovementShape) (dim : width=(r).high+(r).low) (size : HH*rows=(setup).placement.sparse),
      let name:=fun j : Fin N=>((Z).rawAtIndex T rank j).cast size
      let inputMem:=(u).beforeSetupImage ready ((dir).result scene mid)
      let L:=cast (congrArg DescentGL.Layout dim) μ
      let strips:=fun j=>blockValues geo.cut ((r).before geo.size old j) L
      (setup).Moved at_ oldBank name (((setup).sources at_ w oldBank).image inputMem)
        ((setup).assignedDigits geo.host geo.groups (oldBank).which X₀ strips) signals:=by
  let prior:=ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
  have real:=S.previousGeometry G k tail drift degree p age payload prior.nodes prior.arguments oldLanes ctl.base ctl.radix B.age
  have dim : width=(r).high+(r).low:=(sh).dimension.symm.trans real.1.symm
  have geo : (setup).MovementShape:=ResetOutput.movement_shape G S board k tail age p f g drift degree payload
    e previous M nextM C packet prior _ ctl.base ctl.radix B.age priorPos
  have size : HH*rows=(setup).placement.sparse:=by
    change HH*rows=HH*(DescentDenseHostOrder.roster ctl.board k (GroupStage.depthBound venue.degree n f g)).card
    rw [degreeAt,(DescentExteriorReplay.HopTables.reset_public B).1]
    rfl
  have hold:=DateInputs.fromNamed_held_bounds B p drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w (u) ready degreeAt blocksAt oldH capAt positive
  refine ⟨geo,dim,size,?_⟩
  let name:=fun j : Fin N=>((Z).rawAtIndex T rank j).cast size
  let L:=cast (congrArg DescentGL.Layout dim) μ
  have reading : measured (u).originalBasis.base=((DescentExterior.matrixCode L).val:Word w):=by
    rw [show (DescentExterior.matrixCode L).val=(DescentExterior.matrixCode μ).val from native_dimension dim μ]
    exact savedWord
  have issued:=(u).classified_prefix ready scanned publication
  have earliest : floor≤(rc).origin:=by
    obtain ⟨a₁,a₂,a₃⟩:=(a).ingress.order floor
    have front:=((a).occupied start).1
    obtain ⟨e₁,e₂,e₃⟩:=(geom₀).estimator_range (a).payload (a).gain (a).positive
    have startFresh : start≤fresh:=front.trans (e₁.trans (e₂.trans e₃))
    have first : fresh≤(P).saved:=by change fresh≤fresh+_+_;omega
    exact (a₁.trans (a₂.trans a₃)).trans (startFresh.trans (first.trans (PhysicalReset.stencil_saved_before («u»:=u)).le))
  have ni (i : Fin N) : (dir).result scene mid ((dir).inverse.base+i.val)=((name i).val:Word w):=by
    let R:=DescentStageEdgeReceipt.dense ((Z).denseHostRank T rank)
    have returned : (Z).denseHostRank T rank (R.symm i)=i:=R.apply_symm_apply i
    have inverseAt:=inverseWord (R.symm i)
    rw [returned] at inverseAt
    exact inverseAt
  exact (u).moved_after_roots ready mem ((entry₀).image mem) measured mid geo L X₀ old name signals
    floor banks prefixFrame earliest reading innerFrame window signed (fun j hj=>outerFrame j (.inl hj))
    countWord ni hold.2.2.2.1 newFit hold.2.2.1 issued.1 issued.2
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
