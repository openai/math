import OAI.Hierarchy.DescentNamedRelayPacket
import OAI.Hierarchy.DescentNamedTreeValues
import OAI.Hierarchy.DescentNamedPanelPublicCapacity
import OAI.Hierarchy.DescentNamedPublicActor
import OAI.Hierarchy.DescentCapturedRelayRows
import OAI.Hierarchy.DescentNamedRelayObservation
import OAI.Hierarchy.DescentOriginalRelayPadding
import OAI.Hierarchy.DescentCapCalendarPositive

namespace OAI
/-! # The published fallback menu at a terminal with any number of incoming cables -/
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

open DescentPaidResidentCount.Reset DescentResetPublicOperandBook DescentRelativeContacts
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

local notation:max "termSite" t:arg => (blocks B).dst (trunkParent B t)
local notation:max "blockT" t:arg => (termSite t).2
local notation:max "actorT" t:arg => ((denseOrder B) (termSite t).1.2).castLE B.next.valid.host
local notation:max "groupT" t:arg => (termSite t).1.1
local notation:max "tagT" t:arg => (Z).localShape T (termSite t).1.2
local notation:max "sourceT" t:arg => idx (B.frame.host.symm ((T).code t).1)
local notation:max "rawT" t:arg menu:arg paid:arg => (u).menu.publicData sh start count io.hubs g (2^n)
  (stage_ (blockT t)) (regs_ (blockT t)) menu paid (blockT t).val (actorT t) (groupT t)
local notation:max "seenSnap" ss:arg => DateInputs.relay_snapshot (B:=B) (drift:=drift) (degree:=degree)
  (payload:=payload) (e:=e) (previous:=previous) (M:=M) (nextM:=nextM) (oldLanes:=oldLanes)
  (primitiveLanes:=primitiveLanes) (printedBits:=printedBits) (venue:=venue) (io:=io) (floor:=floor) (p:=p) ss
local notation "adjusted" => ({ (pcfg).oldConfig with
  oldDegree := input.placement.degree
  oldCap := input.placement.cap
  donors := 2^(cc+k-(T).commonDepth)
  fineBits := k
  fieldBits := rotor
  residual := res
  maxDepth := GroupStage.depthBound D n f g } : DescentFallbackOperandBranch.Config)
local notation:max "nativeRow" row:arg => relayPhysicalRow (field:=rotor) (query:=q₁) (lanes:=M)
  (batches:=stages₁) (split:=(Z).unit/p) (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift)
  (grain:=p) B row
local notation:max "rankT" snap:arg => DescentSharedBookScan.ranks («a»:=res) («Y»:=2^(Z).n) (D:=input.placement.degree)
  (seenSnap snap).chart (2^(GroupStage.depthBound D n f g)) (GroupStage.depthBound D n f g+2) (seenSnap snap).memory

def DateInputs.OriginalTerminalScene (dd:venue.degree=D) (cd:input.placement.cap=cap)
    (gr:z=S.grainAt G.b p (age+1)) (t:(Z).Fallback) (snap:snapAt)
    (menu:(deck_ (blockT t)).Values head_ gang_) (paid:(deck_ (blockT t)).casts.bits=(C₀).fallbackBits) : Prop :=
  let row:=Config.relabel (cfgEq dd cd gr) B.dimension.symm (rawT t menu paid)
  let head:=(pcfg).oldConfig.header ((pcfg).basic row)
  (adjusted).packet (nativeRow row)=DescentFallbackPeriod.inputs (field:=rotor) (seenSnap snap).stencil
      (seenSnap snap).peers (seenSnap snap).marks (fun host j=>((rankT snap) host j).val) (sourceT t) ((Z).rootBlock T (.inr t)) ∧
    (head 0).val≠0 ∧ (head 2).val=(localRank (Z).graph res (GroupStage.depthBound D n f g) (tagT t)).val ∧
    (tagT t).val=.trunk true ((),(shortName (T).commonDepth ((T).code t)).2)

local notation:max "capturedT" dd:arg cd:arg gr:arg t:arg ss:arg menu:arg paid:arg => DateInputs.OriginalTerminalScene (B:=B) accepted
  drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil
  fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom dd cd gr t ss menu paid
private theorem terminal_enabled_value (c : DescentResetControlRegisters.Chart)
    (mask : Fin c.dims.hosts → Fin c.dims.groups → Cell 1)
    (h₀ : Fin c.dims.hosts) (g₀ : Fin c.dims.groups) (one : 1 < 2^c.bits)
    (present : mask h₀ g₀ ≠ 0) {word : ℕ}
    (valueAt : word=(c.enabled mask (fun _=>1) h₀ g₀).val) : word ≠ 0 := by
  rw [valueAt]
  simp [DescentResetControlRegisters.Chart.enabled,present]
  intro zero
  simp [zero] at one

set_option maxHeartbeats 800000 in
theorem DateInputs.fromNamed_terminal_menu
    (dd:venue.degree=D) (ready:(u).Ready) (mem:Memory w) (cd:input.placement.cap=cap)
    (gr:z=S.grainAt G.b p (age+1)) (μ:DescentGL.Layout (E).dim) (measured dst:Memory w)
    (atDate:DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom dd ready mem cd μ measured dst) (t:(Z).Fallback) :
    ∃(hRaw:HH=(C₀).placement.oldHosts) (sRaw:rows=(C₀).placement.shapes)
      (xCount:2^k=(C₀).placement.blocks)
      (menu:(deck_ (blockT t)).Values head_ gang_) (digits₀:(deck_ (blockT t)).casts.bits=(C₀).fallbackBits),
      (u).PublicValuesRead ready dst ((blockT t).cast xCount) digits₀
        (fun j=>((Z).rawAtIndex T rank j).cast (congrArg₂ Nat.mul hRaw sRaw)) menu ∧
      ∃(hdr:OriginalHeader B input.valid.host (imageOf dd cd).receiver (imageOf dd cd).book measured)
        (xs:OriginalArrays B input.valid.host (v).middle.rootField),
        RootPacket B (imageOf dd cd).receiver (imageOf dd cd).book (imageOf dd cd).prepared measured hdr (imageOf dd cd).sources xs nBits tBits ∧
        capturedT dd cd gr t (root_snapshot B input.valid.host (imageOf dd cd).receiver (imageOf dd cd).book
          (imageOf dd cd).prepared measured hdr xs) menu digits₀ :=by
  obtain ⟨_,_,_,_,R,capture,selfAt,hRaw,sRaw,xCount,all⟩:=atDate
  obtain ⟨menu,digits₀,read,active,regsRead,packets,issued,physical,_,hdr,xs,root,groupAt,orig,_,stored,_,allFields⟩:=
    all (blockT t)
  refine ⟨hRaw,sRaw,xCount,menu,digits₀,read,hdr,xs,root,?_⟩
  have positive : 0<HH:=Nat.zero_lt_of_lt (sourceT t).isLt
  have occupied : 0<cap:=Nat.mul_pos (Chronology.DonorDate.prefix_cap_pos G.b S.rounds g S.height age G.base_pos) (by decide)

  unfold DateInputs.OriginalTerminalScene
  dsimp only
  have ⟨«on»,kind⟩:=relay_terminal_presence B B.next.valid.host t
  let native:=rawT t menu digits₀
  have head:= (Config.relay_relabel (cfgEq dd cd gr) B.dimension.symm (C:=(pcfg).oldConfig) rfl native).1
  have packetRead:=DateInputs.named_terminal_packet (B:=B) accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
    prepared sceneRoom dd cd gr positive t _ menu digits₀ (orig false) groupAt stored (fun j=>by
      have equal := congrFun (congrFun (physical false j (blockT t)) (actorT t)) (groupT t)
      exact (congrArg Fin.val equal).trans (allFields positive false j (blockT t) (actorT t) (groupT t)))
  have capRoom:=DateInputs.named_public_cap_room (input:=input) (ctl:=ctl) (p:=p) drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor cd
  have one : 1<2^rotor :=by omega
  have head0:=(u).menu.public_header_register sh start count io.hubs g (2^n) (stage_ (blockT t)) (regs_ (blockT t))
    menu digits₀ (blockT t).val (actorT t) (groupT t) 0
  have trulyOn : ((config).oldConfig.header ((config).basic native) 0).val≠0 :=by
    rw [head0]
    change (menu.active (actorT t) (groupT t)).val≠0
    exact terminal_enabled_value scaled (occ (blockT t)) (actorT t) (groupT t) one «on» (active _ _)
  have rate:=ResetOutput.fromBoard_tree_caps G S board k tail age p f g drift degree payload e previous M nextM C packet prior_ base₀ occupied
  have limit : rows≤2^(v).sheets.metaBits :=by
    calc rows≤rows+1 :=Nat.le_succ _
         _≤2^Nat.clog 2 (rows+1):=Nat.le_pow_clog (by decide) _
         _≤2^(v).sheets.metaBits:=by
           apply Nat.pow_le_pow_right (by decide)
           rw [sRaw]
           exact (Nat.le_add_left _ _).trans (Nat.le_max_right _ _)
  have shapeFits : ((Z).hostFields T rank (termSite t).1.2).2.val<2^rotor :=
    (((Z).hostFields T rank (termSite t).1.2).2.isLt.trans_le limit).trans_le (Nat.pow_le_pow_right (by decide) rate.2.2)
  have getShape:=(u).menu.public_shape_register sh start count io.hubs g (2^n) (stage_ (blockT t)) (regs_ (blockT t))
    menu digits₀ (blockT t).val (actorT t) (groupT t)
  refine ⟨packetRead,(fun gone=>trulyOn ((head 0).symm.trans gone)),?_,kind⟩
  exact (head 2).trans (getShape.trans ((regsRead 3 _ _).trans
    (shape_register_at B input.valid.host B.next.valid.host (termSite t).1.2 (groupT t) (blockT t) «on» shapeFits)))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
