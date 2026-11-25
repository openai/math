import OAI.Hierarchy.DescentTreeRowPresence
import OAI.Hierarchy.DescentNamedRelaySocket
import OAI.Hierarchy.DescentNamedBankPacket
import OAI.Hierarchy.DescentPrintedFallbackRows

namespace OAI
/-! # The actual dated public fallback row at every installed exceptional bank site -/
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
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤(laneBits ((S.groupWidth k tail age)+k) payload (S.localWalshBits p ((S.groupWidth k tail age)+k) f (quota S.rounds)))-k) (fitsSigned : e≤previous) (fitsCut : previous≤(S.groupWidth k tail age)) (count : Bank)
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
local notation "rawId" => (Z).rawHostRank T rank
local notation "HH" => S.hostSize age
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage
local notation "priorCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal io.wire io.roster v
local notation "sourceRows" => DescentResetCanvasIngress.datedLayout input HH (v).funded.oldLanes
  (priorCPU).lanes (priorCPU).short (v).funded.precision (priorCPU).bits
local notation "oldCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal
  ((sourceRows).tokenAt floor) io.roster v
local notation "geom₀" => (a).chart start
local notation "fresh" => (geom₀).remixEnd (a).payload (a).gain (a).positive
local notation "phys₀" => DescentGLPacked.BankImage.Dated.chart (E).endAddress (geom₀).routedHosts (a).high (a).low (a).bits
local notation "saved" => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim
local notation "chip" => ((phys₀).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length
local notation "digits" => S.resetInputDigits ctl.base ctl.radix age
local notation "peer₀" => PackedFlow.portAt input.placement (input.placement.numberedHeader digits input.vertex).site

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "prev" => fun v=>(Z).placement.b (B.frame.host v)
local notation "U" => (v).actor
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (u).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (u).actor actorBase w)+(dir).ticks scene

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

open DescentSortedRoster
local notation:max "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation:max "heldRoot" degreeAt:arg capAt:arg measured:arg =>
  (∃hdr : ClosedReset.Window.OriginalHeader B input.valid.host (imageOf degreeAt capAt).receiver
        (imageOf degreeAt capAt).book measured,
    ∃x : ClosedReset.Window.OriginalArrays B input.valid.host (v).middle.rootField,
      ClosedReset.Window.RootPacket B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
        (imageOf degreeAt capAt).prepared measured hdr (imageOf degreeAt capAt).sources x nBits tBits)

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
local notation "prior_" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation:max "views" degreeAt:arg => fromBoard_menu (ctl:=ctl) M p drift degree payload e previous nextM base₀ prior_ degreeAt
local notation:max "menuGeometry" degreeAt:arg capAt:arg => mixed_geometry (B:=B) (oldBatch:=2^e) (batch:=M) (calendar:=cal) (paid:=capAt) («v»:=(v))
  (front:=(views degreeAt).1) (sheets:=(views degreeAt).2) (base:=base₀)
local notation "unitTicket" => originalBits D k n (GroupStage.depthBound D n f g) input.placement.cap
  (programCount board (GroupStage.depthBound D n f g)) g
local notation "areaDir" => (⟨(U).endAddress actorBase,HH,rows,chunks (2^(T).commonDepth) (2^e)⟩ :
  DescentResetNewActorDirectory.Layout)
local notation "pg" => ((false,.inr (⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le k) (by decide)⟩,none)) :
  RootPage k (2^n))
local notation:max "transported" _degreeAt:arg _capAt:arg => ((Receiver.IssuedDeck.mk (atlas).directions (atlas).board
  (atlas).primitive pg).reindex (_degreeAt.trans input.branch.symm) B.dimension.symm (calendar_residual B).symm)
local notation:max "actualBook" dd:arg cd:arg => (imageOf dd cd).receiver.issuedBook E (P).S (P).X (P).base (P).bank g
  (transported dd cd).peers (atlas).hostIndex (.lit input.placement.cap) f (quota S.rounds) amp (P).S.total (a).ports
  (Z).graph (Z).width C (atlas).groupDigits (atlas).batches (DescentRecordedRotorLayers.width f input.placement.cap)
  (atlas).factor (transported dd cd).primitive (transported dd cd).page
local notation:max "actualSources" dd:arg cd:arg => (imageOf dd cd).receiver.atlasSources E (P).S (P).X (P).base (P).bank g
  (transported dd cd).peers (atlas).hostIndex (.lit input.placement.cap) f (quota S.rounds) amp (P).S.total (a).ports
  (Z).graph (Z).width C (atlas).groupDigits (atlas).batches (DescentRecordedRotorLayers.width f input.placement.cap)
  (atlas).factor (transported dd cd).primitive (transported dd cd).page
open ClosedReset.Window DescentResetControlRegisters DescentVenueQuantityPlanes
local notation "height₁" => S.hostSize (age+1)
local notation "group₁" => S.groupCount (age+1)
local notation "qbits" => (v).setup.rotorBits
local notation "control" => (v).controlRegisters
local notation "first_" => (v).controlFloor base₀
local notation "last_" => (v).operandFloor base₀
local notation:max "occ" x:arg => fun h g=>actualBit B B.next.valid.host h g x
local notation "scaled" => (⟨quantityDims B 1 HH height₁ (2^e) M,qbits⟩ : DescentResetControlRegisters.Chart)
local notation:max "levelAt_" entry:arg => (Z).placement.b (DescentDenseHostOrder.position (Z).graph (entry).val)

local notation "C₀" => (v).setup
local notation "shelf_" => (v).sheets
local notation:max "stage_" x:arg => (control).live first_ (x:DescentColonies.Block k).val
local notation:max "regs_" x:arg => (control).ports first_ ((a).c/2) (x:DescentColonies.Block k).val ((U).directory actorBase).inverse
  ((U).depths actorBase) ((U).levels actorBase)
local notation:max "deck_" x:arg => OperandMenu.publicPorts («a»:=(a)) sh start count io.hubs g (2^n) (stage_ x) (regs_ x)
local notation "head_" => (C₀).placement.newHosts
local notation "gang_" => (C₀).placement.groups
local notation:max "rows_" x:arg => (b₀:Bool)→Fin ((deck_ x).packets.stage 0 b₀).fields→Fin (deck_ x).packets.blocks→
  Fin head_→Fin gang_→Cell ((deck_ x).casts.width 0)

open DescentPaidResidentCount.Reset DescentResetPublicOperandBook
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation:max "land" edge:arg => (T).home ((old).graph.dst edge)
local notation:max "site" edge:arg => treeReceiver B edge
local notation:max "actor" edge:arg => ((denseOrder B) ((site edge).1.2)).castLE B.next.valid.host
local notation:max "lane" edge:arg => (site edge).1.1
local notation:max "x₁" edge:arg => (site edge).2
local notation:max "occHost" edge:arg => B.frame.host.symm ((Z).rootVertex T edge.1.2)
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
local notation "extent₀" => S.groupWidth k tail age+k
local notation "donors" => 2^(extent₀-(T).commonDepth)
local notation "realCount" => inputCount input.placement.degree donors input.placement.cap (Z).n res
local notation:max "ranks₁" ss:arg => DescentSharedBookScan.ranks («a»:=res) (Y:=2^(Z).n) (D:=input.placement.degree)
  (ss).chart (2^(GroupStage.depthBound D n f g)) (GroupStage.depthBound D n f g+2) (ss).memory
local notation:max "packetAt" cellWidth:arg snap:arg edge:arg => DescentFallbackPeriod.inputs (field:=cellWidth) (snap).stencil (snap).peers (snap).marks
  (fun h j=>((ranks₁ snap) h j).val) (idx (occHost edge)) ((Z).rootBlock T edge.1.2)


local notation:max "seenSnap" ss:arg => DateInputs.relay_snapshot (B:=B) (drift:=drift) (degree:=degree)
  (payload:=payload) (e:=e) (previous:=previous) (M:=M) (nextM:=nextM) (oldLanes:=oldLanes)
  (primitiveLanes:=primitiveLanes) (printedBits:=printedBits) (venue:=venue) (io:=io) (floor:=floor) (p:=p) ss

open DescentChosenRouter
local notation:max "address" side:arg t:arg place:arg => (⟨(side,.inr t),place⟩:(Z).bank.Site)
local notation:max "rrShape" side:arg t:arg place:arg => (Z).localShape T ((Z).placed T ((Z).privateSiteAt T side (.inr t) place))
abbrev DateInputs.OriginalFallbackScene (dd:venue.degree=D) (cd:input.placement.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)
    (gr:z=S.grainAt G.b p (age+1)) (side:Bool) (t:(Z).Fallback) (place:DescentContactTree.Physical.Site ((Z).placement.fallbackBook side t).height) (_snap:snapAt)
    (menu:(deck_ (x₁ (address side t place))).Values head_ gang_) (paid:(deck_ (x₁ (address side t place))).casts.bits=(C₀).fallbackBits) : Prop :=
  let row:=Config.relabel (cfgEq dd cd gr) B.dimension.symm (raw (address side t place) menu paid)
  FallbackRows (p:=p) (field:=rotor) (query:=q₁) (lanes:=M) (nodes:=S.retainedNodes)
    (args:=S.retainedArgumentsAt G drift) (grain:=p) B side t row ∧
    ((pcfg).oldConfig.header ((pcfg).basic row) 0).val≠0 ∧
    ((pcfg).oldConfig.header ((pcfg).basic row) 1).val=input.placement.cap ∧
    ((pcfg).oldConfig.header ((pcfg).basic row) 2).val=
      (localRank (Z).graph res (GroupStage.depthBound D n f g) (rrShape side t place)).val

local notation:max "verifiedScene" dd:arg cd:arg gr:arg side:arg t:arg place:arg ss:arg menu:arg paid:arg => DateInputs.OriginalFallbackScene (B:=B) accepted
  drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil
  fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom dd cd gr side t place ss menu paid

private theorem socket_enabled_value (c : DescentResetControlRegisters.Chart)
    (mask : Fin c.dims.hosts → Fin c.dims.groups → Cell 1)
    (h₀ : Fin c.dims.hosts) (g₀ : Fin c.dims.groups) (one : 1 < 2^c.bits)
    (present : mask h₀ g₀ ≠ 0) {word : ℕ}
    (valueAt : word=(c.enabled mask (fun _=>1) h₀ g₀).val) : word ≠ 0 := by
  rw [valueAt]
  have nz : c.bits ≠ 0 := by intro hz; simp [hz] at one
  simp [DescentResetControlRegisters.Chart.enabled,present,nz]

set_option maxHeartbeats 1000000 in
theorem DateInputs.fallback_scene_of_row
    (dd:venue.degree=D) (cd:input.placement.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256) (gr:z=S.grainAt G.b p (age+1))
    (positive:0<HH) (occupied:0<cap) (elapsed:0<age) (sorted:SourceSorted W input.order)
    (R:(u).MeasuredChannels (Fintype.card B.next.V)) (dst:Memory w) (capture:DateInputs.CaptureRoom R dst)
    (selfAt:CapturedSelf B (u) R)
    (side:Bool) (t:(Z).Fallback) (place:DescentContactTree.Physical.Site ((Z).placement.fallbackBook side t).height) (snap:snapAt)
    (menu:(deck_ (x₁ (address side t place))).Values head_ gang_) (digits₀:(deck_ (x₁ (address side t place))).casts.bits=(C₀).fallbackBits)
    (packets:rows_ (x₁ (address side t place)))
    (issued:menu=(u).issuedPublicValues (x₁ (address side t place)) R B.frame.basis rfl rfl rfl rfl rfl rfl menu.active menu.register packets)
    (getActive:∀h₀ g₀,(menu.active h₀ g₀).val=((scaled).enabled (occ (x₁ (address side t place))) (fun _=>1) h₀ g₀).val)
    (regsRead:∀j h₀ g₀,(menu.register j h₀ g₀).val=((scaled).enabled (occ (x₁ (address side t place)))
      (controlScalar B input.valid.host B.next.valid.host j) h₀ g₀).val)
    (orig:Fin HH→Fin (group₁*2^k)→Cell ((C₀).packets.oldBits*((C₀).packets.stage 0 false).fields))
    (groupAt:group₁*2^k=2^(T).commonDepth)
    (stored:∀h j,(orig h j).val=(savedInput B input.valid.host snap h (j.cast groupAt)).val)
    (reads:∀j,(menu.packet false j (x₁ (address side t place)) (actor (address side t place)) (lane (address side t place))).val=
      ((DescentSIMDLookup.encode (C₀).packets.oldBits ((C₀).packets.stage 0 false).fields).symm
        (orig ((Z).packetOwner T rank positive (actor (address side t place))) (finProdFinEquiv (lane (address side t place),x₁ (address side t place)))) j).val)
    (shapeSize:rows=(C₀).placement.shapes)
    : verifiedScene dd cd gr side t place snap menu digits₀ :=by
  unfold DateInputs.OriginalFallbackScene
  intro rawRow
  have ⟨activeSite,hostSite⟩:=tree_row_presence B B.next.valid.host side t place
  let native:=raw (address side t place) menu digits₀
  let row:=Config.relabel (cfgEq dd cd gr) B.dimension.symm native
  have head:= (Config.relay_relabel (cfgEq dd cd gr) B.dimension.symm (C:=(pcfg).oldConfig) rfl native).1
  have treeRead :=DateInputs.fromNamed_descent_tree_values (B:=B) accepted drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom dd cd gr occupied R dst capture selfAt (x₁ (address side t place)) menu digits₀ packets issued (actor (address side t place)) (lane (address side t place))
  have packetRead:=DateInputs.named_bank_packet (B:=B) accepted drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
    dd cd gr positive (address side t place) snap menu digits₀ orig groupAt stored reads
  have capRoom:=DateInputs.named_public_cap_room (input:=input) (ctl:=ctl) (p:=p) drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor cd
  have one : 1<2^rotor := (show 1 ≤ input.placement.cap from cd.symm ▸ occupied).trans_lt capRoom
  have head0:=(u).menu.public_header_register sh start count io.hubs g (2^n) (stage_ (x₁ (address side t place))) (regs_ (x₁ (address side t place)))
    menu digits₀ (x₁ (address side t place)).val (actor (address side t place)) (lane (address side t place)) 0
  have trulyOn : ((config).oldConfig.header ((config).basic native) 0).val≠0 :=by
    rw [head0]
    change (menu.active (actor (address side t place)) (lane (address side t place))).val≠0
    exact socket_enabled_value scaled (occ (x₁ (address side t place)))
      (actor (address side t place)) (lane (address side t place)) one activeSite (getActive _ _)
  have capacity:=DateInputs.cap_from_public_registers (B:=B) drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom (x₁ (address side t place)) menu capRoom getActive (regsRead 0) (actor (address side t place)) (lane (address side t place)) trulyOn
  have rate:=ResetOutput.fromBoard_tree_caps G S board k tail age p f g drift degree payload e previous M nextM C packet prior_ base₀ occupied
  have limit : rows≤2^(v).sheets.metaBits :=by
    calc rows≤rows+1 :=Nat.le_succ _
         _≤2^Nat.clog 2 (rows+1):=Nat.le_pow_clog (by decide) _
         _≤2^(v).sheets.metaBits:=by
           apply Nat.pow_le_pow_right (by decide)
           rw [shapeSize]
           exact (Nat.le_add_left _ _).trans (Nat.le_max_right _ _)
  have shapeFits : ((Z).hostFields T rank (site (address side t place)).1.2).2.val<2^rotor :=
    (((Z).hostFields T rank (site (address side t place)).1.2).2.isLt.trans_le limit).trans_le (Nat.pow_le_pow_right (by decide) rate.2.2)
  have getShape:=(u).menu.public_shape_register sh start count io.hubs g (2^n) (stage_ (x₁ (address side t place))) (regs_ (x₁ (address side t place)))
    menu digits₀ (x₁ (address side t place)).val (actor (address side t place)) (lane (address side t place))
  have fieldRows : FallbackRows (p:=p) (field:=rotor) (query:=q₁) (lanes:=M) (nodes:=S.retainedNodes)
      (args:=S.retainedArgumentsAt G drift) (grain:=p) B side t row :=by
    apply calibrated_fallback_printed_rows (p:=p) (field:=rotor) (query:=q₁) (lanes:=M) (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) (grain:=p) (currentBatch:=stages₁) (calibrated:=(funded_units B accepted gr).symm) B Fin.valEmbedding input.valid.host (seenSnap snap) side t row
      (lane (address side t place)) (x₁ (address side t place)) (bank_coarse_block B (address side t place)) elapsed sorted (by exact packetRead)
      (treeRead.1.trans (bank_self_word B B.next.valid.host (address side t place))) height₁ M rotor
    exact treeRead.2
  refine ⟨fieldRows,(fun gone=>trulyOn ((head 0).symm.trans gone)),(head 1).trans capacity,?_⟩
  have regShape := shape_register_at (oldM:=2^e) (M:=M) B input.valid.host B.next.valid.host (site (address side t place)).1.2
    (lane (address side t place)) (x₁ (address side t place)) activeSite shapeFits
  exact ((head 2).trans (getShape.trans ((regsRead 3 _ _).trans regShape))).trans
    (congrArg (fun hostValue => (localRank (Z).graph res (GroupStage.depthBound D n f g)
      ((Z).localShape T hostValue)).val) hostSite)

theorem DateInputs.fromNamed_fallback_rows
    (dd:venue.degree=D) (ready:(u).Ready) (mem:Memory w) (cd:input.placement.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)
    (gr:z=S.grainAt G.b p (age+1)) (μ:DescentGL.Layout (E).dim) (measured dst:Memory w)
    (atDate:DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom dd ready mem cd μ measured dst) (elapsed:0<age) (sorted:SourceSorted W input.order)
    (side:Bool) (t:(Z).Fallback) (place:DescentContactTree.Physical.Site ((Z).placement.fallbackBook side t).height) :
    ∃(hRaw:HH=(C₀).placement.oldHosts) (sRaw:rows=(C₀).placement.shapes)
      (xCount:2^k=(C₀).placement.blocks)
      (menu:(deck_ (x₁ (address side t place))).Values head_ gang_) (digits₀:(deck_ (x₁ (address side t place))).casts.bits=(C₀).fallbackBits),
      (u).PublicValuesRead ready dst ((x₁ (address side t place)).cast xCount) digits₀
        (fun j=>((Z).rawAtIndex T rank j).cast (congrArg₂ Nat.mul hRaw sRaw)) menu ∧
      ∃(hdr:OriginalHeader B input.valid.host (imageOf dd cd).receiver (imageOf dd cd).book measured)
        (xs:OriginalArrays B input.valid.host (v).middle.rootField),
        RootPacket B (imageOf dd cd).receiver (imageOf dd cd).book (imageOf dd cd).prepared measured hdr (imageOf dd cd).sources xs nBits tBits ∧
        verifiedScene dd cd gr side t place (root_snapshot B input.valid.host (imageOf dd cd).receiver (imageOf dd cd).book
          (imageOf dd cd).prepared measured hdr xs) menu digits₀ :=by
  obtain ⟨_,_,_,_,R,capture,selfAt,hRaw,sRaw,xCount,all⟩:=atDate
  obtain ⟨menu,digits₀,read,active,regsRead,packets,issued,physical,_,hdr,xs,root,groupAt,orig,_,stored,_,allFields⟩:=
    all (x₁ (address side t place))
  refine ⟨hRaw,sRaw,xCount,menu,digits₀,read,hdr,xs,root,?_⟩
  have positive : 0<HH:=Nat.zero_lt_of_lt (idx (occHost (address side t place))).isLt
  have occupied : 0<cap:=Nat.mul_pos (Chronology.DonorDate.prefix_cap_pos G.b S.rounds g S.height age G.base_pos) (by decide)
  refine DateInputs.fallback_scene_of_row (B:=B) accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
    prepared sceneRoom dd cd gr positive occupied elapsed sorted R dst capture selfAt side t place _ menu digits₀ packets issued active regsRead
    (orig false) groupAt stored ?_ sRaw
  intro j
  have sameCell := congrFun (congrFun (physical false j (x₁ (address side t place)))
    (actor (address side t place))) (lane (address side t place))
  exact (congrArg Fin.val sameCell).trans (allFields positive false j
    (x₁ (address side t place)) (actor (address side t place)) (lane (address side t place)))


end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
