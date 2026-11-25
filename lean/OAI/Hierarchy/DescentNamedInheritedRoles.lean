import OAI.Hierarchy.DescentNamedInheritedBasis
import OAI.Hierarchy.DescentNamedInheritedRoot
import OAI.Hierarchy.DescentNamedPrimitiveVenue
import OAI.Hierarchy.DescentMatchedPublicOrigins
import OAI.Hierarchy.DescentScheduledInheritedTokens

namespace OAI
/-! # The inherited primitive register at a selected, scheduled reset -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentResetGates DescentEpochTagKeys
open DescentActorRaster DescentCommonHost DescentRecordedRotorLayers DescentColonies DescentFallbackPeriod
open DescentPackedColony DescentPackedWalsh DescentSIMDLookup DescentGL DescentPackedZip
open DescentKernelHistory DescentBundleHistory DescentPrimitivePalette DescentLocalArchiveOrder
open DescentOperandStateBanks DescentPacking.PackedMatch.Local.Stage
open DescentSixParty.ClosedReset.Window Reached.NodeCells
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 10000
set_option maxHeartbeats 2200000

open scoped Fin.CommRing

private theorem pitchPacking (v : DescentResetRetainedSetup.Layout) {c k h u : ℕ}
    (pitch : v.CalendarPitch c k h u) : v.matrixLanes*v.donors=2^v.low := by
  have axes := DescentResetRetainedSetup.Layout.CalendarPitch.geometry v pitch
  exact (congrArg₂ Nat.mul axes.2.2.2.1 axes.2.1).trans axes.2.2.1.symm

private theorem layoutCode_cast {a b : ℕ} (h : a=b) (L : DescentGL.Layout a) :
    (DescentExterior.matrixCode (cast (congrArg DescentGL.Layout h) L)).val=
      (DescentExterior.matrixCode L).val:=by cases h;rfl

private theorem layout_cast_heq {a b : ℕ} (h : a=b) (L : DescentGL.Layout a) :
    HEq (cast (congrArg DescentGL.Layout h) L) L:=by cases h;rfl

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (p drift degree payload : ℕ) (ordinary : ℕ→Dated.Ordinary)
    (ports : DatePorts) (floor w : ℕ) (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "op" => RotorSpec.ofRates ctl
local notation "s" => S.firstWidth G.b p
local notation "Z₀" => S.grainAt G.b p 0
local notation "old" => ports.venue
local notation "io" => ports.io
local notation "cap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "CC" => S.groupWidth k tail age
local notation "HH" => S.hostSize age
local notation "prev" => NativePitch.resetCut S k tail p f payload age
local notation "pitch" => NativePitch.incoming S k tail p f payload ordinary (age+1)
local notation "bits₀" => printedBits G s Z₀ op
local notation "e" => receiverCut G S board k tail age p f g drift degree payload prev pitch C ctl.bitsR
  ports.operandLanes ports.roleLanes bits₀ old
local notation "fc" => scheduled_cut_origin G S board k tail age p f g drift degree payload ordinary op s Z₀
  ports.operandLanes ports.roleLanes old
local notation "pc" => preceding_cut S k tail p f payload age
local notation "base" => ports.priorStart k floor
local notation "hist₀" => (ports.afterPad k floor).archive
local notation "publisher" => priorArchivePhase G S board k tail age p f g drift degree payload ordinary op s Z₀ ports floor w
local notation "a" => (scheduledAtPorts G S board k tail age p f g drift degree payload ordinary op s Z₀ ports floor).inner
local notation "v" => (a).successor
local notation "move" => (v).roleTransfer
local notation "V" => (move).transfer
local notation "chart" => (v).primitive.chart
local notation "start" => (a).stageStart base
local notation "Est" => (a).estimator start
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap
local notation "height" => GroupStage.depthBound (old).degree n f g
variable (capacity : (old).cap=cap)
    (space : ScheduledCodeRoom G S board k tail age p f g drift degree payload ordinary op s Z₀
      ports.operandLanes ports.roleLanes old io base w hist₀)
local notation "u" => DatePorts.resetInputs G S board k tail age p f g drift degree payload ordinary op s Z₀
  ports floor w space
local notation "cy" => DatePorts.resetFinalInputs G S board k tail age p f g drift degree payload ordinary op s Z₀
  ports floor w capacity space
local notation "ing" => (a).ingress
local notation "entry" m:arg => ((ing).phase base w (io).hubs (fun x=>(io).atoms x.val) (fun t=>(io).wire t.1.val t.2.val)).image
  ((publisher).image m)
local notation "dated" => (u).shape
local notation "dep" => GroupStage.depthBound D n f g
local notation "shapeCount" => (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth) dep).card
local notation "geom" => (show (V).CalendarPitch CC k payload (v).retainedRoleUnit from ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩)
local notation "calendar" => DescentResetRetainedSetup.Layout.CalendarPitch.geometry (V) geom

variable (archive : Archive W) (early : Local archive.bit) (menu : Runnable F op)
    (labels : Encoding (Label G s Z₀ op) (dictionary G op menu p) archive.bit)
    (hp : 0<p) (whole : p∣B.reset.unit)
local notation "newBits" => (resetArchive B p hp whole archive).bit
local notation "num" => DescentLocalArchiveOrder.reset B p hp whole archive early
local notation "gate" => reachedInput G s Z₀ op menu B hp whole archive labels
local notation "slot" x:arg j:arg h':arg g':arg => whereAt B.next newBits num ((x).cast (cy).roleBlocks) ((j).cast (cy).roleNodes) h' g'

/-- Keep the original measured stencil and held root packet of the same
scheduled origin receipt used to obtain the public operand rows. -/
theorem DateInputs.matched_inherited_origins (degreeAt : (old).degree=D) (ready : (u).Ready)
    (m : Memory w) (capAt : input.placement.cap=cap)
    (receipt : RegisterTimeline.MatchedPublicOrigins board op B p drift degree payload w ordinary
      ⟨ports,floor⟩ space rfl rfl rfl rfl rfl HEq.rfl rfl degreeAt ready m capAt) :
    ∃(μ : DescentGL.Layout (Est).dim) (measured postActors : Memory w),
      DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e prev (2^e) pitch
        ports.operandLanes ports.roleLanes bits₀ old io base w fc fc pc (hist₀).count
        (hist₀).nodeBase (hist₀).arguments (hist₀).seed space.prepared space.scene degreeAt ready
        ((publisher).image m) capAt μ measured postActors:=by
  obtain ⟨postActors,_,atActors⟩:=receipt
  obtain ⟨μ,measured,original⟩:=atActors
  exact ⟨μ,measured,postActors,original⟩

include accepted in
/-- The selector, the physical root packet, the previous role pages and the compact
directory used here all belong to this reset of the original chronological archive. -/
theorem FinalInputs.fromNamed_inherited_roles
    (homes : (old).hosts=HH) (blocks : (old).k=k) (groups : (old).groups=S.groupCount age)
    (degreeAt : (old).degree=D) (capAt : input.placement.cap=cap)
    (widths : DatePorts.ArchiveWidths G S op ports k tail p drift degree payload age)
    (args : ports.argumentsPerNode=(if age=0 then 3*(s/p) else S.retainedArgumentsAt G drift))
    (room : DatePorts.RangeRoom ports input archive.bit) {R : ℕ} (shape : WorldShape p R archive.bit)
    (m mid dst : Memory w) (held : ports.held input floor m) (counted : ports.archive.count.base<floor)
    (wireShelf : ports.WireRoom w floor) (native : ports.ArchiveFits k floor) (roleLanes : 0<ports.roleLanes)
    {ptr : NodeOrder.All archive.bit→ℕ→Pointer}
    {flags : Fin (2^(old).k)→Fin ports.nodes→Fin ports.operandHosts→Fin (old).groups→ℕ}
    (oldRows : DatePorts.ArchiveRead ports input archive.bit early room shape op labels.atNode ptr flags m)
    (sized : ports.RoleRows) (hubFit : (io).hubs.Fits w floor)
    (atomFit : ∀x : Fin (2^(ing).k),((io).atoms x.val).Fits w floor)
    (wireFit : ∀j : (ing).signed.Slot,((io).wire j.1.val j.2.val).Fits w floor)
    (ready : (u).Ready) (safe : (cy).Room)
    (run : (PhysicalReset.date cy).Runs (entry m) dst) (operands : (u).throughOperandDate.Runs (entry m) mid)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (epoch : hist=s) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (v).funded.oldLanes (v).funded.precision base
      (input.venueRoster input.valid.host) ((publisher).image m))
    (popFit : (hist₀).count.Fits w base) (popRead : (publisher).image m (hist₀).count.base=(Fintype.card input.V:Computability.VPVNP.BurstRAM.Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),((io).wire x.val j.val).Fits w base ∧
      HH*chunks (S.groupCount age) (v).funded.oldLanes≤((io).wire x.val j.val).size)
    (oldPos : 0<(v).funded.oldLanes) (oldWidth : (v).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(Est).low)
    (score : 3*(Est).dim+((Est).precision+Nat.clog 2 (Est).hosts)+2≤w)
    (live : 0<amp) (degreePos : 0<32*Nat.clog 2 (2*(old).degree))
    (headerBits : Nat.clog 2 ((Est).dim+2)+((Est).dim+S.censusBits p)≤w) (hostBits : HH<2^w)
    (ranksFit : (old).degree*2^height<2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*(old).degree)) g n≤w)
    (degreeFits : (old).degree+1<2^w) (laneRoom : 2^e≤w) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd base<2^w)
    (μ : DescentGL.Layout (Est).dim) (measured postActors : Memory w)
    (origins : DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e prev (2^e) pitch
      ports.operandLanes ports.roleLanes bits₀ old io base w fc fc pc (hist₀).count
      (hist₀).nodeBase (hist₀).arguments (hist₀).seed space.prepared space.scene degreeAt ready
      ((publisher).image m) capAt μ measured postActors) :
    ∀(x:Fin (chart).blocks)(j:Fin (chart).nodes),Source ((cy).roles.retained x j)
      (fun h' g'=>DescentResetPrimitivePage.oldWord ((slot x j h' g').elim .padding gate))
      (chart).lanes ((cy).roleInput mid):=by
  obtain ⟨won,scan,_,⟨hdr,xs,packet⟩,_⟩:=origins
  have previous:=scheduled_archive_inherited_tokens G S board k tail age p f g drift degree payload ordinary op
    ports floor w capacity space input early room shape labels.atNode m homes blocks groups widths args held counted
    wireShelf (capacity.trans capAt.symm) native roleLanes oldRows sized hubFit atomFit wireFit entryFits
  have roots:=DateInputs.fromNamed_inherited_root (B:=B) drift degree payload e prev (2^e) pitch
    ports.operandLanes ports.roleLanes bits₀ old io base w fc fc pc (hist₀).count (hist₀).nodeBase
    (hist₀).arguments (hist₀).seed space.prepared space.scene degreeAt capAt ready rfl rfl small word
    ceiling capacity gr fee (entry m) measured hdr xs packet scan
  have saved:=DateInputs.fromNamed_inherited_basis accepted drift degree payload e prev (2^e) pitch
    ports.operandLanes ports.roleLanes bits₀ old io base w fc fc pc (hist₀).count (hist₀).nodeBase
    (hist₀).arguments (hist₀).seed space.prepared space.scene degreeAt ready ((publisher).image m) gr fee capAt
    epoch branch seen popFit popRead wireRoom oldPos oldWidth entryFits low score live degreePos headerBits hostBits
    ranksFit namesFit degreeFits laneRoom μ measured scan won
  obtain ⟨_,_,countNow,inverseNow,countRoom,hostRoom,inverseRoom,_⟩:=
    fromNamed_primitive_venue B drift degree payload e prev (2^e) pitch ports.operandLanes ports.roleLanes bits₀
      old io base w fc fc pc (hist₀).count (hist₀).nodeBase (hist₀).arguments (hist₀).seed space.prepared
      space.scene cy accepted degreeAt blocks homes (Nat.two_pow_pos _) ready safe ((publisher).image m)
      gr fee capAt epoch branch seen popFit popRead wireRoom oldPos oldWidth entryFits low score live degreePos
      headerBits hostBits ranksFit namesFit degreeFits laneRoom operands
  have pitchAt : (V).CalendarPitch CC k payload (v).retainedRoleUnit := geom
  have pitchInfo := DescentResetRetainedSetup.Layout.CalendarPitch.geometry (V) pitchAt
  have dim : (Est).dim=(V).high+(V).low:=(dated).dimension.symm.trans pitchInfo.1.symm
  let basis:=cast (congrArg DescentGL.Layout dim) μ
  have inheritedBasis : HEq basis B.frame.basis:=(layout_cast_heq dim μ).trans won
  have key:=((cy).original_basis ready safe scan run operands).trans saved
  have physicalCode : (DescentExterior.matrixCode basis).val=(DescentExterior.matrixCode μ).val:=layoutCode_cast dim μ
  have savedBasis := key.trans (congrArg (fun n : ℕ => (n : Computability.VPVNP.BurstRAM.Word w)) physicalCode.symm)
  have area : 2^((V).high+(V).low)=(V).groups*(V).blocks:=by
    calc
      _ = 2^(CC+k) := congrArg (fun z : ℕ => 2^z) pitchInfo.1
      _ = 2^CC*2^k := Nat.pow_add _ _ _
      _ = S.groupCount age*2^k := congrArg (·*2^k) (S.group_power ctl.base ctl.radix age)
      _ = _ := rfl
  have cutRoom : (V).cut≤(V).high+(V).low := pitchAt.cut.le.trans ((Nat.le_add_right _ k).trans_eq pitchInfo.1.symm)
  have targets : shapeCount=(move).shapes:=B.public_hub_slots.trans (by
    change (DescentDenseHostOrder.roster board k dep).card=(DescentDenseHostOrder.roster board k height).card
    rw [degreeAt])
  have recipients : (move).groups*(move).blocks=(V).grouped:=by
    change S.groupCount (age+1)*2^k=2^CC
    rw [S.group_cut B.age,pow_add,S.group_power ctl.base ctl.radix]
  have priorNodes : ∀ site,Fintype.card (archive.bit.recipe site).Node≤(V).previousNodes:=fun site=>(room.capacity site).trans_eq widths.nodes
  have lanes : 0<(V).gatherLanes:=by rw [pitchAt.gather];exact Nat.two_pow_pos _
  have packed : (V).matrixLanes*(V).donors=2^(V).low:=by
    exact pitchPacking (V) (c:=CC) (k:=k) (h:=payload) («u»:=(v).retainedRoleUnit) pitchAt
  have fieldRoom : 2*k+n+2≤(v).middle.rootField:=by
    change 2*k+n+2≤ResetMiddle.fieldWidth (old).degree cap n k height
    unfold ResetMiddle.fieldWidth ResetMiddle.senderWidth
    omega
  have fieldLive : 0<(v).middle.rootField := (Nat.zero_lt_succ (2*k+n+1)).trans_le fieldRoom
  intro x j
  exact inherited_from_history B _ _ _ measured hdr _ xs cy rfl pitchInfo.1 B.commonDepth.symm
    (degreeAt.trans input.branch.symm) capAt.symm rfl archive early rfl rfl area cutRoom basis inheritedBasis
    priorNodes targets rfl rfl rfl recipients hp whole packet fieldRoom fieldLive menu labels rfl rfl rfl rfl
    safe ready run operands roots.1 pitchInfo.2.2.1 lanes (Nat.two_pow_pos _) roleLanes packed
    (by rw [pitchInfo.2.2.2.1];exact lanes) (by rw [pitchAt.decoded];exact lanes) (Nat.two_pow_pos _)
    savedBasis previous.1 previous.2.1 previous.2.2 roots.2 rfl rfl HEq.rfl rfl
    (congrArg (fun j=>GroupStage.depthBound j n f g) degreeAt) countNow inverseNow countRoom hostRoom inverseRoom x j

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
