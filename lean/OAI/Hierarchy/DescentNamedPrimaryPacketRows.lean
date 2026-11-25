import OAI.Hierarchy.DescentIssuedRangeRequests
import OAI.Hierarchy.DescentNamedPrimaryShape
import OAI.Hierarchy.DescentRegisteredWindowSelectors
import OAI.Hierarchy.DescentCalendarRetainedSensors

namespace OAI
/-! # Measured primary selectors on the same original reset request panel -/
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
variable {F Vertex : Type} [Field F] {d : ℕ} {abits : Vertex→ℕ} {W : MarkedWorld F d Vertex abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "physicalDate" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "stepOut" => (physicalDate).successor
local notation "start" => (physicalDate).stageStart floor
local notation "base₀" => (physicalDate).rebased start
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
local notation "rc" => (physicalDate).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (physicalDate).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (physicalDate).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (stepOut).middle.stop base₀
local notation "early" => (stepOut).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (stepOut).front.SceneRoom early ((stepOut).issuedScene base₀ older) w)
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
local notation "priorCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal io.wire io.roster v
local notation "sourceRows" => DescentResetCanvasIngress.datedLayout input HH (stepOut).funded.oldLanes
  (priorCPU).lanes (priorCPU).short (stepOut).funded.precision (priorCPU).bits
local notation "oldCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal
  ((sourceRows).tokenAt floor) io.roster v
local notation "geom₀" => (physicalDate).chart start
local notation "fresh" => (geom₀).remixEnd (physicalDate).payload (physicalDate).gain (physicalDate).positive
local notation "phys₀" => DescentGLPacked.BankImage.Dated.chart (E).endAddress (geom₀).routedHosts (physicalDate).high (physicalDate).low (physicalDate).bits
local notation "saved" => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim
local notation "chip" => ((phys₀).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length
local notation "digits" => S.resetInputDigits ctl.base ctl.radix age
local notation "peer₀" => PackedFlow.portAt input.placement (input.placement.numberedHeader digits input.vertex).site

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "prev" => fun v=>(Z).placement.b (B.frame.host v)
local notation "U" => (stepOut).actor
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (u).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (u).actor actorBase w)+(dir).ticks scene

local notation "entry₀" => (physicalDate).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

open DescentSortedRoster
local notation "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "heldRoot" degreeAt:arg capAt:arg measured:arg =>
  (∃hdr : ClosedReset.Window.OriginalHeader B input.valid.host (imageOf degreeAt capAt).receiver
        (imageOf degreeAt capAt).book measured,
    ∃x : ClosedReset.Window.OriginalArrays B input.valid.host (stepOut).middle.rootField,
      ClosedReset.Window.RootPacket B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
        (imageOf degreeAt capAt).prepared measured hdr (imageOf degreeAt capAt).sources x nBits tBits)
open DescentSixParty.ClosedReset.Window DescentOperandRootPull DescentSixParty.PackedFlow.Channels
local notation "setup" => (stepOut).setup
local notation "r" => (setup).retained
local notation "at_" => (stepOut).operandFloor base₀
local notation "M₁" => 2^e
local notation "coarse" => (T).commonDepth
local notation "span" => (Z).k-coarse
local notation "field" => (stepOut).middle.rootField
local notation "A₁" => input.placement
local notation "rn₁" => (calendar_residual B).symm
local notation "half₁" => (show (physicalDate).c/2=cap by change (2*cap)/2=cap;omega)
local notation "Ksig" => Fin (setup).strip→Fin (setup).placement.oldHosts→Fin ((setup).placement.groups*(setup).placement.blocks)→Cell (setup).signedBits

local notation "ctrl" => (stepOut).controlRegisters
local notation "controlStart" => (stepOut).controlFloor base₀
local notation "liveAt" x => (ctrl).live controlStart (x:Fin (stepOut).receiver.blocks).val
local notation "regsAt" x => (ctrl).ports controlStart ((physicalDate).c/2) (x:Fin (stepOut).receiver.blocks).val
  ((U).directory actorBase).inverse ((U).depths actorBase) ((U).levels actorBase)
local notation "deck" x => OperandMenu.publicPorts (a:=physicalDate) sh start count io.hubs g (2^n) (liveAt x) (regsAt x)
local notation "primaryWords" => DateInputs.PrimaryWordsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
  venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
local notation "primaryCtl" => DateInputs.PrimaryControlsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
  venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
local notation "movementAt" => DateInputs.MovementAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
  venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
local notation "issuedFields" => DateInputs.IssuedFieldsAt G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom
local notation "issuedRead" => DateInputs.fromNamed_issued_ordinal G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom

open DescentSixParty.Chronology DescentSixParty.Chronology.DatePorts
open DescentLocalArchiveOrder DescentKernelHistory DescentPrimitivePalette DescentRetainedRangeDigits
open DescentFallbackShapeTable DescentRelativeContacts DescentIssuedFallbackPanel DescentPaidResidentCount.Reset
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
local notation "im_" => imageOf degreeAt capAt
variable (measured : Memory w) (hdr : OriginalHeader B input.valid.host (im_).receiver (im_).book measured)
    (xs : OriginalArrays B input.valid.host field) (X : (setup).seven.Packets)
    (matrixRead : ∀v hi, (X v hi).val=(DescentSIMDLookup.encode field (DescentRotorWindowArchive.count (A₁).degree (2^span) (A₁).cap)
      (calendar_sender_matrix B M₁ field (im_).receiver (im_).book (im_).prepared measured hdr xs v
        ⟨hi.val,by rw [B.commonDepth];exact hi.isLt⟩)).val)
variable (oldA : Archive W) (num : Local oldA.bit) (hp : 0<p) (whole : p∣(Z).unit)
local notation "after_" => (resetArchive B p hp whole oldA).bit
local notation "newNum" => DescentLocalArchiveOrder.reset B p hp whole oldA num
variable (ports : DatePorts) (places : DatePorts.RangeRoom ports B.next after_)
    (block : Fin (2^ports.venue.k)) (node : Fin ports.nodes) (rack : Fin ports.operandHosts) (group : Fin ports.venue.groups)
    (now : NodeOrder.All after_) (old : NodeOrder.All oldA.bit)
    (slotAt : DatePorts.slotAt ports B.next after_ newNum places block node rack group=some now)
    (source : resetOrigin B hp whole oldA now=Sum.inl old) (size : HH*rows=(setup).placement.sparse)
local notation "term" => (T).home old.1
local notation "shapeCode" => DescentFallbackShapeTable.cell span (shortName coarse ((T).code term)).2
local notation "sourceHost" => B.frame.host.symm ((T).code term).1
local notation "carrier" => idx sourceHost
local notation "rootHi" => (Z).rootBlock T (.inr term)
local notation "cutEq" => (show (r).cut=coarse from B.commonDepth.symm)
local notation "nativeHi" => (rootHi).cast (congrArg (2^·) cutEq).symm
local notation "nd" => (u).menu.donors.trans (congrArg (2^·) rn₁)
local notation "dirs" => fun j : Fin (Fintype.card B.next.V)=>((Z).rawAtIndex T rank j).cast size
local notation:max "physical_" present:arg => (setup).placement.shape (dirs ⟨rack.val,present⟩)
local notation:max "fine_" lo:arg => ((lo:Fin (r).donors).cast nd).cast (congrArg (fun t=>2^(t-coarse)) B.keyWidth)
local notation "small_" => B.frame.enough.trans (Nat.sub_le ..)
local notation:max "source_" lo:arg => (rearrange B.frame.basis).symm (join small_ rootHi lo)
local notation:max "bits_" lo:arg => xs.stencil carrier rootHi lo
local notation "rootWord" => DescentSIMDLookup.encode field (DescentRotorWindowArchive.count (A₁).degree (2^span) (A₁).cap)
  (calendar_sender_matrix B M₁ field (im_).receiver (im_).book (im_).prepared measured hdr xs carrier rootHi)

include slotAt source matrixRead in
/-- The retained actor, its true old carrier and both original order predicates come from the
same measured packet for all physical arguments of the original node. -/
theorem DateInputs.named_primary_packet_rows :
    ∃present:rack.val<Fintype.card B.next.V,
      let tok:=physical_ present
      (u).bank.which tok=some shapeCode ∧ (u).menu.keep tok=true ∧
      ((setup).placement.previous (dirs ⟨rack.val,present⟩)).val=(carrier).val ∧
      group.val*2^k+block.val=(rootHi).val ∧ node.val=(newNum now.1 now.2).val ∧
      (X carrier nativeHi).val=(rootWord).val ∧ (setup).seven.degree=input.placement.degree ∧
      (setup).seven.capacity=input.placement.cap ∧ (setup).seven.packetBits=field ∧ 0<field ∧
      (∀lo,bits_ lo<2^field) ∧
      ownerAt setup (u).bank.which X tok carrier nativeHi=(fun d=>decide (bits_ (fine_ d)/2=shapeCode)) ∧
      priorAt setup X carrier nativeHi=(fun d j=>decide (source_ (fine_ d)<source_ (fine_ j))) ∧
      ∀lo,bits_ lo/2=DescentPlainTerminal.Suffix.Stencil.shapeCode ((cc+k)-coarse) (2^(Z).n)
        (DescentPlainTerminal.Suffix.fieldsRelative coarse (ClosedReset.Recorded.originalCell (reset:=B) sourceHost (source_ lo))):=by
  obtain ⟨live,target,kept,host_,cursor_,n₀⟩:=DateInputs.named_primary_shape (B:=B)
    drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w
    fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom oldA num hp whole
    ports places block node rack group now old slotAt source degreeAt size
  let tok:=physical_ live
  have packet_ : (X carrier nativeHi).val=(rootWord).val:=matrixRead carrier nativeHi
  have deg : (setup).seven.degree=input.placement.degree:=degreeAt.trans input.branch.symm
  have cap_ : (setup).seven.capacity=input.placement.cap:=(u).menu.capacity.trans ((half₁).trans capAt.symm)
  have width_ : (setup).seven.packetBits=field:=rfl
  have plus (lo) : bits_ lo+1<2^field:=by rw [xs.localRead];exact xs.fits _
  have fit lo : bits_ lo<2^field:=Nat.lt_trans (Nat.lt_succ_self _) (plus lo)
  have positive : 0<field:=by
    by_contra absent
    have no : field=0:=Nat.eq_zero_of_not_pos absent
    have test := plus (0:DescentColonies.Block ((cc+k)-coarse))
    have two : 1 < 2^field := (Nat.le_add_left 1 _).trans_lt test
    rw [no,pow_zero] at two
    exact (Nat.lt_irrefl 1) two
  obtain ⟨owns,order⟩:=registered_window_selectors B M₁ field (im_).receiver (im_).book (im_).prepared measured
    hdr xs setup (u).bank.which X tok carrier nativeHi carrier rootHi shapeCode target deg nd cap_ width_ packet_ positive fit
  exact ⟨live,target,kept,host_,cursor_,n₀,packet_,deg,cap_,width_,positive,fit,owns,order,
    primary_original_stencil B xs sourceHost rootHi⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
