import OAI.Hierarchy.DescentNamedPublicSocketConfig
import OAI.Hierarchy.DescentRelayOperandRelabel
import OAI.Hierarchy.DescentRelaySavedPacket
import OAI.Hierarchy.DescentRelaySocketObserved
import OAI.Hierarchy.DescentRootObservationWidth
import OAI.Hierarchy.DescentPublicRelayPacket

namespace OAI
/-! # The fallback packet at an original incoming relay on the named date -/
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
variable (fitsStencil : e≤(laneBits ((S.groupWidth k tail age)+k) payload (S.localWalshBits p ((S.groupWidth k tail age)+k) f (quota S.rounds)))-k) (fitsSigned : e≤previous) (fitsCut : previous≤(S.groupWidth k tail age)) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
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

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage

local notation "res" => (Z).k-(T).commonDepth
local notation "U" => (v).actor

open DescentSortedRoster

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
open ClosedReset.Window DescentResetControlRegisters DescentVenueQuantityPlanes
local notation "group₁" => S.groupCount (age+1)
local notation "control" => (v).controlRegisters
local notation "first_" => (v).controlFloor base₀

local notation "C₀" => (v).setup
local notation:max "stage_" x:arg => (control).live first_ (x:DescentColonies.Block k).val
local notation:max "regs_" x:arg => (control).ports first_ ((a).c/2) (x:DescentColonies.Block k).val ((U).directory actorBase).inverse
  ((U).depths actorBase) ((U).levels actorBase)
local notation:max "deck_" x:arg => OperandMenu.publicPorts («a»:=a) sh start count io.hubs g (2^n) (stage_ x) (regs_ x)
local notation "head_" => (C₀).placement.newHosts
local notation "gang_" => (C₀).placement.groups

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
local notation "extent₀" => S.groupWidth k tail age+k
local notation "donors" => 2^(extent₀-(T).commonDepth)
local notation "realCount" => inputCount input.placement.degree donors input.placement.cap (Z).n res
local notation:max "ranks₁" ss:arg => DescentSharedBookScan.ranks («a»:=res) («Y»:=2^(Z).n) (D:=input.placement.degree)
  (ss).chart (2^(GroupStage.depthBound D n f g)) (GroupStage.depthBound D n f g+2) (ss).memory
local notation:max "packetAt" cellWidth:arg snap:arg edge:arg => DescentFallbackPeriod.inputs (field:=cellWidth) (snap).stencil (snap).peers (snap).marks
  (fun h j=>((ranks₁ snap) h j).val) (idx (occHost edge)) ((Z).rootBlock T (.inr (land edge)))

theorem DateInputs.named_relay_packet_width : (v).middle.rootField≤rotor :=
  (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

local notation:max "terminalSite" t:arg => (blocks B).dst (trunkParent B t)
local notation:max "xT" t:arg => (terminalSite t).2
local notation:max "hostT" t:arg => ((denseOrder B) (terminalSite t).1.2).castLE B.next.valid.host
local notation:max "laneT" t:arg => (terminalSite t).1.1
local notation:max "rootT" t:arg => B.frame.host.symm ((T).code t).1
local notation:max "rawT" t:arg menu:arg paid:arg => (u).menu.publicData sh start count io.hubs g (2^n)
  (stage_ (xT t)) (regs_ (xT t)) menu paid (xT t).val (hostT t) (laneT t)
local notation:max "packetT" cellWidth:arg snap:arg t:arg => DescentFallbackPeriod.inputs (field:=cellWidth) (snap).stencil (snap).peers (snap).marks
  (fun h j=>((ranks₁ snap) h j).val) (idx (rootT t)) ((Z).rootBlock T (.inr t))

set_option maxHeartbeats 700000 in
theorem DateInputs.named_terminal_packet
    (dd:venue.degree=D) (cd:input.placement.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256) (gr:z=S.grainAt G.b p (age+1))
    (positive:0<HH) (t:(Z).Fallback) (snap:snapAt)
    (menu:(deck_ (xT t)).Values head_ gang_)
    (digits₀:(deck_ (xT t)).casts.bits=(C₀).fallbackBits)
    (orig:Fin HH→Fin (group₁*2^k)→Cell ((C₀).packets.oldBits*((C₀).packets.stage 0 false).fields))
    (groupAt:group₁*2^k=2^(T).commonDepth)
    (stored:∀h j,(orig h j).val=(savedInput B input.valid.host snap h (j.cast groupAt)).val)
    (reads:∀j,(menu.packet false j (xT t) (hostT t) (laneT t)).val=
      ((DescentSIMDLookup.encode (C₀).packets.oldBits ((C₀).packets.stage 0 false).fields).symm
        (orig ((Z).packetOwner T rank positive (hostT t)) (finProdFinEquiv (laneT t,xT t))) j).val) :
    let row:=Config.relabel (cfgEq dd cd gr) B.dimension.symm (rawT t menu digits₀)
    let physical:=relayPhysicalRow (field:=rotor) (query:=q₁) (lanes:=M) (batches:=stages₁) (split:=(Z).unit/p)
      (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) (grain:=p) B row
    let adjusted:=({ (pcfg).oldConfig with
      oldDegree := input.placement.degree
      oldCap := input.placement.cap
      «donors» := donors
      fineBits := k
      fieldBits := rotor
      residual := res
      maxDepth := GroupStage.depthBound D n f g } : DescentFallbackOperandBranch.Config)
    adjusted.packet physical=packetT rotor snap t :=by
  intro row physical adjusted
  have parts:=Config.relay_relabel (cfgEq dd cd gr) B.dimension.symm
    (relay_socket_config (field:=rotor) (query:=q₁) (lanes:=M) (batches:=stages₁)
      (split:=(Z).unit/p) (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) B)
    (rawT t menu digits₀)
  have half : (2*cap)/2=cap :=by omega
  have packetDims : ((C₀).packets.stage 0 false).fields=realCount :=by
    apply relay_packet_fields B
    · exact dd.trans input.branch.symm
    · exact cd.symm
    · rfl
    · exact (funded_residual B).symm
  have keyDims : inputCount (config).oldDegree (config).donors (config).oldCap
      (v).middle.rotorBits (config).residual=realCount :=by
    change inputCount venue.degree (2^k) ((2*cap)/2) n k=_
    rw [half]
    exact packetDims
  funext key
  apply Fin.ext
  let j:=(DescentFallbackPeriod.number key).cast packetDims.symm
  let slot:=(DescentFallbackPeriod.number key).cast keyDims.symm
  let typed : Input (config).oldDegree (config).donors (config).oldCap (v).middle.rotorBits (config).residual :=
    DescentFallbackPeriod.number.symm slot
  have address : (DescentFallbackPeriod.number typed).val=(DescentFallbackPeriod.number key).val :=by
    simp [typed,slot]
  have valid : (DescentFallbackPeriod.number typed).val<((C₀).packets.stage 0 false).fields :=by
    rw [address,packetDims];exact (DescentFallbackPeriod.number key).isLt
  have decoded:=relay_saved_terminal B input.valid.host B.next.valid.host positive snap t rfl rfl groupAt rfl packetDims orig stored key
  have firstRead:=reads j
  have sameIndex : (⟨(DescentFallbackPeriod.number typed).val,valid⟩:Fin ((C₀).packets.stage 0 false).fields)=j :=
    Fin.ext address
  let readAt (j₀ : Fin ((C₀).packets.stage 0 false).fields) : ℕ :=
    (menu.packet false j₀ (xT t) (hostT t) (laneT t)).val
  have sameRead := congrArg readAt sameIndex
  have fieldRoom : (menu.packet false ⟨_,valid⟩ (xT t) (hostT t) (laneT t)).val<
      2^(deck_ (xT t)).casts.bits :=by
    exact lt_of_eq_of_lt sameRead (lt_of_eq_of_lt firstRead (((DescentSIMDLookup.encode _ _).symm _ j).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) (show (C₀).packets.oldBits≤(deck_ (xT t)).casts.bits from
        (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))))))
  have current:=(u).menu.public_fallback_word sh start count io.hubs g (2^n) (stage_ (xT t))
    (regs_ (xT t)) menu digits₀ (xT t).val (hostT t) (laneT t) typed valid (xT t).isLt fieldRoom
  have grows : (v).middle.rootField≤rotor :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have widened:=snap.inputs_widen grows (rootT t) ((Z).rootBlock T (.inr t)) key
  exact (parts.2.2 key typed address.symm).trans (current.trans (sameRead.trans (firstRead.trans (decoded.trans widened.symm))))

theorem DateInputs.named_relay_packet
    (dd:venue.degree=D) (cd:input.placement.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256) (gr:z=S.grainAt G.b p (age+1))
    (positive:0<HH) (edge:(old).graph.Edge) (snap:snapAt)
    (menu:(deck_ (x₁ edge)).Values head_ gang_)
    (digits₀:(deck_ (x₁ edge)).casts.bits=(C₀).fallbackBits)
    (orig:Fin HH→Fin (group₁*2^k)→Cell ((C₀).packets.oldBits*((C₀).packets.stage 0 false).fields))
    (groupAt:group₁*2^k=2^(T).commonDepth)
    (stored:∀h j,(orig h j).val=(savedInput B input.valid.host snap h (j.cast groupAt)).val)
    (reads:∀j,(menu.packet false j (x₁ edge) (actor edge) (lane edge)).val=
      ((DescentSIMDLookup.encode (C₀).packets.oldBits ((C₀).packets.stage 0 false).fields).symm
        (orig ((Z).packetOwner T rank positive (actor edge)) (finProdFinEquiv (lane edge,x₁ edge))) j).val) :
    let row:=Config.relabel (cfgEq dd cd gr) B.dimension.symm (raw edge menu digits₀)
    let physical:=relayPhysicalRow (field:=rotor) (query:=q₁) (lanes:=M) (batches:=stages₁) (split:=(Z).unit/p)
      (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) (grain:=p) B row
    let adjusted:=({ (pcfg).oldConfig with
      oldDegree := input.placement.degree
      oldCap := input.placement.cap
      «donors» := donors
      fineBits := k
      fieldBits := rotor
      residual := res
      maxDepth := GroupStage.depthBound D n f g } : DescentFallbackOperandBranch.Config)
    adjusted.packet physical=packetAt rotor snap edge :=
  DateInputs.named_terminal_packet (B:=B) accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom dd cd gr positive (land edge) snap menu digits₀ orig groupAt stored reads

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
