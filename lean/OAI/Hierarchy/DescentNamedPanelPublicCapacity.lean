import OAI.Hierarchy.DescentNamedResetDateInputs
import OAI.Hierarchy.DescentDatedPublicQueryRoom
import OAI.Hierarchy.DescentDateTaggedOrdinals
import OAI.Hierarchy.DescentCapturedActorEvent
import OAI.Hierarchy.DescentNamedOperandRequests
import OAI.Hierarchy.DescentNamedReachedCandidates

namespace OAI
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
local notation "rows" => (DescentDenseHostOrder.roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "U" => (v).actor

open DescentSortedRoster

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
open DescentSharedCableNames
open DescentResetTrunks
local notation "C₀" => (v).setup
local notation "H₁" => S.hostSize (age+1)

local notation "ctrl" => (v).controlRegisters
local notation "controlStart" => (v).controlFloor base₀
local notation "liveAt" x:arg => (ctrl).live controlStart (x:Fin (v).receiver.blocks).val
local notation "regsAt" x:arg => (ctrl).ports controlStart ((a).c/2) (x:Fin (v).receiver.blocks).val
  ((U).directory actorBase).inverse ((U).depths actorBase) ((U).levels actorBase)
local notation "deck" x:arg => OperandMenu.publicPorts («a»:=a) sh start count io.hubs g (2^n) (liveAt x) (regsAt x)

local notation "cfg" => publicOperands (u).atlas (u).roots (u).menu.payload
local notation "operandValues" x:arg menu:arg => (u).menu.publicData sh start count io.hubs g (2^n)
  (liveAt x) (regsAt x) menu rfl ((x):Fin (v).receiver.blocks).val

/-- The two public facts needed by the retained field join, on the native public operand bank. -/
def DateInputs.PublicOperandRowsAt (ok : (u).Ready) (after : Memory w) : Prop :=
  ∀(size : HH*rows=(C₀).placement.sparse) (x : Fin (v).receiver.blocks),
    ∃menu : (deck x).Values (C₀).placement.newHosts (C₀).placement.groups,
      (u).PublicValuesRead ok after (x.cast (u).operandBlocks) rfl
        (fun j=>((Z).rawAtIndex T rank j).cast size) menu ∧
      ∀h gr,((cfg).oldConfig.header ((cfg).basic ((operandValues x menu) h gr)) 0).val≠0 →
        ((cfg).reg ((operandValues x menu) h gr) 0).val=input.placement.cap

local notation "pubRows" => DateInputs.PublicOperandRowsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
open ClosedReset.Window DescentResetControlRegisters DescentVenueQuantityPlanes
local notation "qbits" => (v).setup.rotorBits
local notation "occ" x:arg => fun h g=>actualBit B B.next.valid.host h g x
local notation "scaled" => (⟨quantityDims B 1 HH H₁ (2^e) M,qbits⟩ : DescentResetControlRegisters.Chart)

/-- The installed fallback directory provides enough control bits for the previous dated cap. -/
theorem DateInputs.named_public_cap_room (capAt : input.placement.cap=cap) :
    input.placement.cap<2^qbits:=by
  let pool:=DescentPackedPrivateMenu.fieldBound board k (GroupStage.depthBound venue.degree n f g)
    (2^k*(2*cap)) (DescentRecordedRotorLayers.width f cap) C packet
  have room : 2^k*(2*cap)≤pool:=Nat.le_max_left ..
  have bitsRoom : ProtocolRAMPurchaseSampler.bits pool≤qbits:=
    ((Nat.le_max_right ..).trans (Nat.le_max_right ..)).trans (Nat.le_max_right ..)
  have many : 1≤2^k:=Nat.two_pow_pos _
  rw [capAt]
  calc
    cap≤1*(2*cap):=by omega
    _≤2^k*(2*cap):=Nat.mul_le_mul_right _ many
    _≤pool:=room
    _<2^(ProtocolRAMPurchaseSampler.bits pool):=ProtocolRAMPurchaseSampler.lt_span pool
    _≤2^qbits:=Nat.pow_le_pow_right (by decide) bitsRoom

/-- The actual enabled control-zero word reads the old capacity on every nonempty row. -/
theorem DateInputs.cap_from_public_registers (x : Fin (v).receiver.blocks)
    (menu : (deck x).Values (C₀).placement.newHosts (C₀).placement.groups)
    (capRoom : input.placement.cap<2^qbits)
    (active : ∀h gr,(menu.active h gr).val=((scaled).enabled (occ x) (fun _=>1) h gr).val)
    (zero : ∀h gr,(menu.register 0 h gr).val=((scaled).enabled (occ x)
      (controlScalar B input.valid.host B.next.valid.host 0) h gr).val)
    (h : Fin (C₀).placement.newHosts) (gr : Fin (C₀).placement.groups)
    (seen : ((cfg).oldConfig.header ((cfg).basic ((operandValues x menu) h gr)) 0).val≠0) :
    ((cfg).reg ((operandValues x menu) h gr) 0).val=input.placement.cap:=by
  have bit:= (u).menu.public_header_register sh start count io.hubs g (2^n) (liveAt x) (regsAt x) menu rfl x.val h gr 0
  have num:= (u).menu.public_control_registers sh start count io.hubs g (2^n) (liveAt x) (regsAt x) menu rfl x.val h gr 0
  have rowNonzero : actualBit B B.next.valid.host h gr x≠0:=by
    intro blank
    apply seen
    rw [bit]
    change (menu.active h gr).val=0
    rw [active]
    simp [DescentResetControlRegisters.Chart.enabled,blank]
  obtain ⟨site,atHost⟩ : ∃site,controlReceiver B B.next.valid.host h=some site:=by
    cases found : controlReceiver B B.next.valid.host h with
    | none=>exact (rowNonzero (control_receiver_none B B.next.valid.host h found gr x)).elim
    | some site=>exact ⟨site,rfl⟩
  have controlZero : controlScalar B input.valid.host B.next.valid.host 0 h = input.placement.cap := by
    unfold controlScalar
    rw [atHost]
    rfl
  rw [num,zero]
  simp only [DescentResetControlRegisters.Chart.enabled, ite_eq_right rowNonzero]
  exact (congrArg (fun n : ℕ => (n : Cell qbits).val) controlZero).trans (Fin.val_cast_of_lt capRoom)

/-- Package the original public menu and its two joined words for the signed field selector. -/
theorem DateInputs.public_rows_from_registers (ready : (u).Ready) (after : Memory w)
    (capRoom : input.placement.cap<2^qbits)
    (size : HH*rows=(C₀).placement.sparse)
    (read : ∀x : Fin (v).receiver.blocks,∃menu : (deck x).Values (C₀).placement.newHosts (C₀).placement.groups,
      (u).PublicValuesRead ready after (x.cast (u).operandBlocks) rfl
        (fun j=>((Z).rawAtIndex T rank j).cast size) menu ∧
      (∀h gr,(menu.active h gr).val=((scaled).enabled (occ x) (fun _=>1) h gr).val) ∧
      ∀j h gr,(menu.register j h gr).val=((scaled).enabled (occ x)
        (controlScalar B input.valid.host B.next.valid.host j) h gr).val) :
    pubRows ready after:=by
  intro _ x
  obtain ⟨menu,loaded,active,word⟩:=read x
  exact ⟨menu,loaded,DateInputs.cap_from_public_registers (B:=B) drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
    prepared sceneRoom x menu capRoom active (word 0)⟩

open DescentGL DescentGLPacked DescentGLPacked.BankImage DescentSortedRoster
open ClosedReset.Window DescentResetLocalRoster DescentResetCandidatePair DescentSharedCableNames DescentResetTrunks

local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (a).estimator start
local notation "rawId" => (Z).rawHostRank T rank
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (u).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (u).actor actorBase w)+(dir).ticks scene
local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)
local notation:max "datePeerSlots" degreeProof:arg =>
  (show (v).front.peer.hosts=HH*(DescentDenseHostOrder.roster (Z).graph res (GroupStage.depthBound D n f g)).card from by
    change HH*(DescentDenseHostOrder.roster board k Ht).card=_
    rw [degreeProof]
    exact congrArg (HH*·) (calendar_palette B))
local notation "A₁" => (v).receiver
local notation "G₁" => S.groupCount (age+1)
local notation "ST" => (v).sheetsStart base₀
local notation "plan" => (v).linkedRankInputs (u).sectors ST
local notation "draw" => (v).renderFromRanks plan base₀
local notation "physicalRack" => rackOf B (((Z).denseHostRank T rank).trans (Fin.castLEEmb B.next.valid.host))

set_option maxHeartbeats 1600000 in
/-- The reached reset panels record measured actors, their operand requests and the preceding signed rows. -/
def DateInputs.OperandPanelsAt (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
    (ready : (u).Ready) (mem : Memory w) (archived : (C₀).retained.Values) : Prop :=
    let peerWidth : (v).front.peer.hosts=HH*rows := (datePeerSlots degreeAt)
    ∃(μ : DescentGL.Layout (E).dim) (measured dst : Memory w),HEq μ B.frame.basis ∧
      measured (P).saved=((DescentExterior.matrixCode μ).val:Word w) ∧
      ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
        count (E).depthRows (rc).stencil book measured ∧
      ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w).Exec ((entry₀).image mem) measured
        ((a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w) ∧
      (pub).Exec measured dst ticks ∧
      DateInputs.OperandRequestsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
      venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom degreeAt capAt ready archived μ measured dst ∧
      ∃R : (u).MeasuredChannels (Fintype.card B.next.V), DateInputs.CaptureRoom R dst ∧
        (∀v₀ : B.next.V,DescentSortedRoster.present (DescentResetPeerUnionRAM.selfPeers (ClosedReset.Window.renumberPeer peerWidth R.near))
          (rawId v₀)=(insert v₀ ((Z).emittedNear T v₀)).map rawId) ∧
        (∀v₀ : B.next.V,DescentSortedRoster.present (ClosedReset.Window.renumberPeer peerWidth R.near)
          (rawId v₀)=((Z).emittedNear T v₀).map rawId) ∧
        (u).throughOperandDate.Runs ((entry₀).image mem) ((u).sheetsResult ready dst) ∧
    ∃ (hx : (A₁).blocks=2^k) (hj : (A₁).candidates=totalLocal B)
      (gg : (A₁).groups=G₁) (capacityAt : (A₁).capacity=B.next.placement.cap)
      (alignedHosts : (A₁).hosts=(v).sheets.hosts),
      (∀i j,let x:=(v).operandIndex (u).operand i
        Source ((v).previous (u).operand draw base₀ i j)
          (fun h g=>(ResetOutput.pointerField x.2.1).elim (0:Cell (A₁).signedBits) (fun f=>
             (DescentNextSignedWindow.Native.fields ((physicalRack (h.cast alignedHosts)).bind (fun z=>
                candidateRows B (fieldNames B) ((g.cast gg,z),x.1.cast hx) (j.cast (congrArg (2*·) hj)))) f:ℕ)))
          (A₁).lanes ((u).operandEntry ready dst))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
