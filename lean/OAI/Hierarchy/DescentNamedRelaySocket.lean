import OAI.Hierarchy.DescentNamedRelayPacket
import OAI.Hierarchy.DescentNamedTreeValues
import OAI.Hierarchy.DescentNamedPanelPublicCapacity
import OAI.Hierarchy.DescentNamedPublicActor
import OAI.Hierarchy.DescentCapturedRelayRows
import OAI.Hierarchy.DescentRelayRowPresence
import OAI.Hierarchy.DescentCapCalendarPositive

namespace OAI
/-! # Named original incoming relay sockets at the captured public RAM row -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
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
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rootPhase (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w)).PreparedFits (atlasBook (namedAtlas G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) count) (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w))
  (sceneRoom : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).front.SceneRoom (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).actorEnd (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor))) (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).issuedScene (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor)) (namedOriginals G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count)) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "HH" => S.hostSize age
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage
local notation "geom₀" => (a).chart start
local notation "fresh" => (geom₀).remixEnd (a).payload (a).gain (a).positive
local notation "saved" => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "U" => (v).actor

open DescentSortedRoster
local notation:max "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
open ClosedReset.Window DescentResetControlRegisters DescentVenueQuantityPlanes
local notation "height₁" => S.hostSize (age+1)
local notation "group₁" => S.groupCount (age+1)
local notation "qbits" => (v).setup.rotorBits
local notation "control" => (v).controlRegisters
local notation "first_" => (v).controlFloor base₀
local notation "prior_" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation:max "occ" x:arg => fun h g=>actualBit B B.next.valid.host h g x
local notation "scaled" => (⟨quantityDims B 1 HH height₁ (2^e) M,qbits⟩ : DescentResetControlRegisters.Chart)

local notation "C₀" => (v).setup
local notation:max "stage_" x:arg => (control).live first_ (x:DescentColonies.Block k).val
local notation:max "regs_" x:arg => (control).ports first_ ((a).c/2) (x:DescentColonies.Block k).val ((U).directory actorBase).inverse
  ((U).depths actorBase) ((U).levels actorBase)
local notation:max "deck_" x:arg => OperandMenu.publicPorts («a»:=a) sh start count io.hubs g (2^n) (stage_ x) (regs_ x)
local notation "head_" => (C₀).placement.newHosts
local notation "gang_" => (C₀).placement.groups
local notation:max "rows_" x:arg => (b₀:Bool)→Fin ((deck_ x).packets.stage 0 b₀).fields→Fin (deck_ x).packets.blocks→
  Fin head_→Fin gang_→Cell ((deck_ x).casts.width 0)

open DescentPaidResidentCount.Reset DescentResetPublicOperandBook
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation:max "land" edge:arg => (T).home ((old).graph.dst edge)
local notation:max "site" edge:arg => (blocks B).dst (trunkParent B (land edge))
local notation:max "actor" edge:arg => ((denseOrder B) ((site edge).1.2)).castLE B.next.valid.host
local notation:max "lane" edge:arg => (site edge).1.1
local notation:max "x₁" edge:arg => (site edge).2
local notation:max "occHost" edge:arg => B.frame.host.symm ((T).code (land edge)).1
local notation "rotor" => (v).setup.rotorBits
local notation "q₁" => (v).setup.queryBits
local notation "stages₁" => ResetInput.calendarLanes S G.b (age+1)
local notation "pcfg" => publicOperandConfig B rotor q₁ M stages₁ ((Z).unit/p) S.retainedNodes
  (S.retainedArgumentsAt G drift) p
local notation "config" => publicOperands (u).atlas (u).roots (u).menu.payload
local notation:max "cfgEq" dd:arg cd:arg gr:arg => (DateInputs.fromNamed_public_socket_config (B:=B) accepted drift degree payload e
  previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
  previousArguments initial prepared sceneRoom dd cd gr).2
local notation:max "raw" edge:arg menu:arg cut₀:arg => (u).menu.publicData sh start count io.hubs g (2^n) (stage_ (x₁ edge))
  (regs_ (x₁ edge)) menu cut₀ (x₁ edge).val (actor edge) (lane edge)
local notation "snapAt" => PaddedSnapshot B input.valid.host (v).middle.rootField

open DescentRelativeContacts
local notation "split" => (Z).unit/p
local notation:max "face_" edge:arg arg:arg => if (arg:Fin (2*split)).val< split then trunkParent B (land edge)
  else stemParent B (true,edge)
local notation:max "amount_" edge:arg arg:arg => if (arg:Fin (2*split)).val< split then earlierIncoming B edge*split+(arg).val
  else (arg).val-split
local notation:max "marked_" edge:arg arg:arg => if (arg:Fin (2*split)).val< split then ((T).code (land edge)).2.2.isSome else false
local notation:max "rrShape" edge:arg => (Z).localShape T (site edge).1.2

def DateInputs.relay_snapshot (snap:snapAt) :=
  (snap.reorder (other:=input.order.trans Fin.valEmbedding)
    (congrArg (fun ord:W.graph.Edge↪Fin (Fintype.card W.graph.Edge)=>ord.trans Fin.valEmbedding) B.order_eq)).widen
    (large:=rotor) ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))

local notation:max "seenSnap" ss:arg => DateInputs.relay_snapshot (B:=B) (drift:=drift) (degree:=degree)
  (payload:=payload) (e:=e) (previous:=previous) (M:=M) (nextM:=nextM) (oldLanes:=oldLanes)
  (primitiveLanes:=primitiveLanes) (printedBits:=printedBits) (venue:=venue) (io:=io) (floor:=floor) (p:=p) ss

abbrev DateInputs.OriginalRelayScene (dd:venue.degree=D) (cd:input.placement.cap=cap)
    (gr:z=S.grainAt G.b p (age+1)) (edge:(old).graph.Edge) (snap:snapAt)
    (menu:(deck_ (x₁ edge)).Values head_ gang_) (paid:(deck_ (x₁ edge)).casts.bits=(C₀).fallbackBits) : Prop :=
  let row:=Config.relabel (cfgEq dd cd gr) B.dimension.symm (raw edge menu paid)
  RelayRows (field:=rotor) (query:=q₁) (lanes:=M) (batches:=stages₁) («split»:=split) (nodes:=S.retainedNodes)
    (args:=S.retainedArgumentsAt G drift) (grain:=p) (M:=M) B input.valid.host Fin.valEmbedding (seenSnap snap) B.next.valid.host edge row ∧
    ((pcfg).oldConfig.header ((pcfg).basic row) 0).val≠0 ∧
    ((pcfg).oldConfig.header ((pcfg).basic row) 1).val=input.placement.cap ∧
    ((pcfg).oldConfig.header ((pcfg).basic row) 2).val=
      (localRank (Z).graph res (GroupStage.depthBound D n f g) (rrShape edge)).val ∧
    (rrShape edge).val=.trunk true ((),(shortName (T).commonDepth ((T).code (land edge))).2)

local notation:max "verifiedScene" dd:arg cd:arg gr:arg edge:arg ss:arg menu:arg paid:arg => DateInputs.OriginalRelayScene (B:=B) accepted
  drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil
  fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom dd cd gr edge ss menu paid

private theorem relay_enabled_value (c : DescentResetControlRegisters.Chart)
    (mask : Fin c.dims.hosts → Fin c.dims.groups → Cell 1)
    (h₀ : Fin c.dims.hosts) (g₀ : Fin c.dims.groups) (one : 1 < 2^c.bits)
    (present : mask h₀ g₀ ≠ 0) {word : ℕ}
    (valueAt : word=(c.enabled mask (fun _=>1) h₀ g₀).val) : word ≠ 0 := by
  rw [valueAt]
  simp [DescentResetControlRegisters.Chart.enabled,present]
  intro zero
  simp [zero] at one

set_option maxHeartbeats 800000 in
theorem DateInputs.named_relay_scene_of_row
    (dd:venue.degree=D) (cd:input.placement.cap=cap) (gr:z=S.grainAt G.b p (age+1))
    (positive:0<HH) (occupied:0<cap)
    (R:(u).MeasuredChannels (Fintype.card B.next.V)) (dst:Memory w) (capture:DateInputs.CaptureRoom R dst)
    (selfAt:CapturedSelf B (u) R)
    (edge:(old).graph.Edge) (snap:snapAt)
    (menu:(deck_ (x₁ edge)).Values head_ gang_) (digits₀:(deck_ (x₁ edge)).casts.bits=(C₀).fallbackBits)
    (packets:rows_ (x₁ edge))
    (issued:menu=(u).issuedPublicValues (x₁ edge) R B.frame.basis rfl rfl rfl rfl rfl rfl menu.active menu.register packets)
    (getActive:∀h₀ g₀,(menu.active h₀ g₀).val=((scaled).enabled (occ (x₁ edge)) (fun _=>1) h₀ g₀).val)
    (regsRead:∀j h₀ g₀,(menu.register j h₀ g₀).val=((scaled).enabled (occ (x₁ edge))
      (controlScalar B input.valid.host B.next.valid.host j) h₀ g₀).val)
    (orig:Fin HH→Fin (group₁*2^k)→Cell ((C₀).packets.oldBits*((C₀).packets.stage 0 false).fields))
    (groupAt:group₁*2^k=2^(T).commonDepth)
    (stored:∀h j,(orig h j).val=(savedInput B input.valid.host snap h (j.cast groupAt)).val)
    (reads:∀j,(menu.packet false j (x₁ edge) (actor edge) (lane edge)).val=
      ((DescentSIMDLookup.encode (C₀).packets.oldBits ((C₀).packets.stage 0 false).fields).symm
        (orig ((Z).packetOwner T rank positive (actor edge)) (finProdFinEquiv (lane edge,x₁ edge))) j).val)
    (shapeSize:rows=(C₀).placement.shapes)
    : verifiedScene dd cd gr edge snap menu digits₀ :=by
  unfold DateInputs.OriginalRelayScene
  intro rawRow
  have ⟨«on»,kind⟩:=relay_row_presence B B.next.valid.host edge
  let native:=raw edge menu digits₀
  let row:=Config.relabel (cfgEq dd cd gr) B.dimension.symm native
  have head:= (Config.relay_relabel (cfgEq dd cd gr) B.dimension.symm (C:=(pcfg).oldConfig) rfl native).1
  have fieldReads:=DateInputs.fromNamed_descent_tree_values (B:=B) accepted drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom dd cd gr occupied R dst capture selfAt (x₁ edge) menu digits₀ packets issued (actor edge) (lane edge)
  have packetRead:=DateInputs.named_relay_packet (B:=B) accepted drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
    dd cd gr positive edge snap menu digits₀ orig groupAt stored reads
  have capRoom:=DateInputs.named_public_cap_room (input:=input) (ctl:=ctl) (p:=p) drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor cd
  have one : 1<2^rotor :=by omega
  have head0:=(u).menu.public_header_register sh start count io.hubs g (2^n) (stage_ (x₁ edge)) (regs_ (x₁ edge))
    menu digits₀ (x₁ edge).val (actor edge) (lane edge) 0
  have trulyOn : ((config).oldConfig.header ((config).basic native) 0).val≠0 :=by
    rw [head0]
    change (menu.active (actor edge) (lane edge)).val≠0
    exact relay_enabled_value scaled (occ (x₁ edge)) (actor edge) (lane edge) one «on» (getActive _ _)
  have capacity:=DateInputs.cap_from_public_registers (B:=B) drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom (x₁ edge) menu capRoom getActive (regsRead 0) (actor edge) (lane edge) trulyOn
  have rate:=ResetOutput.fromBoard_tree_caps G S board k tail age p f g drift degree payload e previous M nextM C packet prior_ base₀ occupied
  have limit : rows≤2^(v).sheets.metaBits :=by
    calc rows≤rows+1 :=Nat.le_succ _
         _≤2^Nat.clog 2 (rows+1):=Nat.le_pow_clog (by decide) _
         _≤2^(v).sheets.metaBits:=by
           apply Nat.pow_le_pow_right (by decide)
           rw [shapeSize]
           exact (Nat.le_add_left _ _).trans (Nat.le_max_right _ _)
  have shapeFits : ((Z).hostFields T rank (site edge).1.2).2.val<2^rotor :=
    (((Z).hostFields T rank (site edge).1.2).2.isLt.trans_le limit).trans_le (Nat.pow_le_pow_right (by decide) rate.2.2)
  have getShape:=(u).menu.public_shape_register sh start count io.hubs g (2^n) (stage_ (x₁ edge)) (regs_ (x₁ edge))
    menu digits₀ (x₁ edge).val (actor edge) (lane edge)
  refine ⟨⟨packetRead,fieldReads.1,fun y _ ax=>fieldReads.2 (incomingIndex B y) ax⟩,
    (fun gone=>trulyOn ((head 0).symm.trans gone)),(head 1).trans capacity,?_,kind⟩
  exact (head 2).trans (getShape.trans ((regsRead 3 _ _).trans
    (shape_register_at B input.valid.host B.next.valid.host (site edge).1.2 (lane edge) (x₁ edge) «on» shapeFits)))

theorem DateInputs.OriginalRelayScene.socket
    (dd:venue.degree=D) (cd:input.placement.cap=cap) (gr:z=S.grainAt G.b p (age+1))
    (elapsed:0<age) (sorted:SourceSorted W input.order) (edge:(old).graph.Edge) (arg:Fin (2*split))
    (snap:snapAt) (menu:(deck_ (x₁ edge)).Values head_ gang_)
    (digits₀:(deck_ (x₁ edge)).casts.bits=(C₀).fallbackBits) (data_:verifiedScene dd cd gr edge snap menu digits₀) :
    ∃number,∃sock:PublicSocket B (site edge) split (amount_ edge arg) (marked_ edge arg) number,
      sock.face.val.1=face_ edge arg ∧ sock.face.val.2=decide (arg.val< split) ∧
      (config).mixed (u).atlas.board (earlierIncoming B edge) arg.val (raw edge menu digits₀)=
        some (number,amount_ edge arg,1,marked_ edge arg) :=by
  let native:=raw edge menu digits₀
  let row:=Config.relabel (cfgEq dd cd gr) B.dimension.symm native
  obtain ⟨fieldReads,«on»,capWord,shapeWord,kind⟩:=data_
  obtain ⟨number,sock,left,right,observed⟩:=RelayRows.reply (field:=rotor) (query:=q₁) (lanes:=M) (batches:=stages₁) («split»:=(Z).unit/p)
      (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) (grain:=p) (M:=M) B input.valid.host Fin.valEmbedding (seenSnap snap)
    B.next.valid.host elapsed sorted edge arg row fieldReads (rrShape edge) «on» shapeWord kind capWord (funded_units B accepted gr).symm
  have graphEq:=(DateInputs.fromNamed_public_socket_config (B:=B) accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom dd cd gr).1
  exact ⟨number,sock,left,right,(Config.mixed_relabel (cfgEq dd cd gr) B.dimension.symm rfl graphEq native
    arg.val (earlierIncoming B edge)).symm.trans observed⟩

/-- The reached receipt determines every original relay's public menu «on» the same actor memory. -/
theorem DateInputs.fromNamed_relay_rows
    (dd:venue.degree=D) (ready:(u).Ready) (mem:Memory w) (cd:input.placement.cap=cap)
    (gr:z=S.grainAt G.b p (age+1)) (μ:DescentGL.Layout (E).dim) (measured dst:Memory w)
    (atDate:DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom dd ready mem cd μ measured dst) (edge:(old).graph.Edge) :
    ∃(hRaw:HH=(C₀).placement.oldHosts) (sRaw:rows=(C₀).placement.shapes)
      (xCount:2^k=(C₀).placement.blocks)
      (menu:(deck_ (x₁ edge)).Values head_ gang_) (digits₀:(deck_ (x₁ edge)).casts.bits=(C₀).fallbackBits),
      (u).PublicValuesRead ready dst ((x₁ edge).cast xCount) digits₀
        (fun j=>((Z).rawAtIndex T rank j).cast (congrArg₂ Nat.mul hRaw sRaw)) menu ∧
      ∃(hdr:OriginalHeader B input.valid.host (imageOf dd cd).receiver (imageOf dd cd).book measured)
        (xs:OriginalArrays B input.valid.host (v).middle.rootField),
        RootPacket B (imageOf dd cd).receiver (imageOf dd cd).book (imageOf dd cd).prepared measured hdr (imageOf dd cd).sources xs nBits tBits ∧
        verifiedScene dd cd gr edge (root_snapshot B input.valid.host (imageOf dd cd).receiver (imageOf dd cd).book
          (imageOf dd cd).prepared measured hdr xs) menu digits₀ :=by
  obtain ⟨_,_,_,_,R,capture,selfAt,hRaw,sRaw,xCount,all⟩:=atDate
  obtain ⟨menu,digits₀,read,active,regsRead,packets,issued,physical,_,hdr,xs,root,groupAt,orig,_,stored,_,allFields⟩:=
    all (x₁ edge)
  refine ⟨hRaw,sRaw,xCount,menu,digits₀,read,hdr,xs,root,?_⟩
  have positive : 0<HH:=Nat.zero_lt_of_lt (idx (occHost edge)).isLt
  have occupied : 0<cap:=Nat.mul_pos (Chronology.DonorDate.prefix_cap_pos G.b S.rounds g S.height age G.base_pos) (by decide)
  refine DateInputs.named_relay_scene_of_row (B:=B) accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
    prepared sceneRoom dd cd gr positive occupied R dst capture selfAt edge _ menu digits₀ packets issued active regsRead
    (orig false) groupAt stored ?_ sRaw
  intro j
  have equal := congrFun (congrFun (physical false j (x₁ edge)) (actor edge)) (lane edge)
  exact (congrArg Fin.val equal).trans (allFields positive false j (x₁ edge) (actor edge) (lane edge))

/-- Fix the original menu once per fine block. Every incoming cable in that
block uses the same saved packet and public operand observations. -/
theorem DateInputs.fromNamed_relay_menu
    (dd:venue.degree=D) (ready:(u).Ready) (mem:Memory w) (cd:input.placement.cap=cap)
    (gr:z=S.grainAt G.b p (age+1)) (μ:DescentGL.Layout (E).dim) (measured dst:Memory w)
    (atDate:DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom dd ready mem cd μ measured dst) (x:DescentColonies.Block k) :
    ∃(hRaw:HH=(C₀).placement.oldHosts) (sRaw:rows=(C₀).placement.shapes)
      (xCount:2^k=(C₀).placement.blocks) (menu:(deck_ x).Values head_ gang_)
      (paid:(deck_ x).casts.bits=(C₀).fallbackBits),
      (u).PublicValuesRead ready dst (x.cast xCount) paid
        (fun j=>((Z).rawAtIndex T rank j).cast (congrArg₂ Nat.mul hRaw sRaw)) menu ∧
      ∃(hdr:OriginalHeader B input.valid.host (imageOf dd cd).receiver (imageOf dd cd).book measured)
        (xs:OriginalArrays B input.valid.host (v).middle.rootField),
        RootPacket B (imageOf dd cd).receiver (imageOf dd cd).book (imageOf dd cd).prepared measured hdr (imageOf dd cd).sources xs nBits tBits ∧
        ∀(edge:(old).graph.Edge) (atBlock:(x₁ edge)=x),
        let menu₁:(deck_ (x₁ edge)).Values head_ gang_ := atBlock.symm ▸ menu
        let paid₁:(deck_ (x₁ edge)).casts.bits=(C₀).fallbackBits := atBlock.symm ▸ paid
        verifiedScene dd cd gr edge (root_snapshot B input.valid.host (imageOf dd cd).receiver (imageOf dd cd).book
          (imageOf dd cd).prepared measured hdr xs) menu₁ paid₁ :=by
  obtain ⟨_,_,_,_,R,capture,selfAt,hRaw,sRaw,xCount,all⟩:=atDate
  obtain ⟨menu,paid,read,active,regsRead,packets,issued,physical,_,hdr,xs,root,groupAt,orig,_,stored,_,allFields⟩:=all x
  refine ⟨hRaw,sRaw,xCount,menu,paid,read,hdr,xs,root,?_⟩
  intro edge atBlock
  subst x
  have positive : 0<HH:=Nat.zero_lt_of_lt (idx (occHost edge)).isLt
  have occupied : 0<cap:=Nat.mul_pos (Chronology.DonorDate.prefix_cap_pos G.b S.rounds g S.height age G.base_pos) (by decide)
  refine DateInputs.named_relay_scene_of_row (B:=B) accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
    prepared sceneRoom dd cd gr positive occupied R dst capture selfAt edge _ menu paid packets issued active regsRead
    (orig false) groupAt stored ?_ sRaw
  intro j
  have equal := congrFun (congrFun (physical false j (x₁ edge)) (actor edge)) (lane edge)
  exact (congrArg Fin.val equal).trans (allFields positive false j (x₁ edge) (actor edge) (lane edge))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
