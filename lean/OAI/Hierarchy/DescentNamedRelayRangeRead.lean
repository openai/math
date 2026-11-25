import OAI.Hierarchy.DescentIssuedRangeRequests
import OAI.Hierarchy.DescentRelayOperandRelabel
import OAI.Hierarchy.DescentNativeFreshRangePlaces
import OAI.Hierarchy.DescentNativeRelayRanks
import OAI.Hierarchy.DescentObservedRotorFaces

namespace OAI
/-! # The range digit read from a physically measured right-trunk row -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F Pin : Type} [Field F] {d : ℕ} {abits : Pin→ℕ} {W : MarkedWorld F d Pin abits}
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
variable (previousMeta previousArguments : ℕ) (initial : Bool)
set_option hygiene false

local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "HH" => S.hostSize age

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "U" => (v).actor

open DescentSortedRoster
open DescentSixParty.ClosedReset.Window DescentOperandRootPull DescentSixParty.PackedFlow.Channels
local notation "setup" => (v).setup
local notation "r" => (setup).retained

local notation "ctrl" => (v).controlRegisters
local notation "controlStart" => (v).controlFloor base₀
local notation:max "liveAt" x:arg => (ctrl).live controlStart (x:Fin (v).receiver.blocks).val
local notation:max "regsAt" x:arg => (ctrl).ports controlStart ((a).c/2) (x:Fin (v).receiver.blocks).val
  ((U).directory actorBase).inverse ((U).depths actorBase) ((U).levels actorBase)
local notation:max "deck" x:arg => OperandMenu.publicPorts («a»:=a) sh start count io.hubs g (2^n) (liveAt x) (regsAt x)

open DescentSixParty.Chronology.DatePorts
open DescentLocalArchiveOrder DescentKernelHistory DescentPrimitivePalette DescentRetainedRangeDigits
open DescentFallbackShapeTable DescentRelativeContacts DescentIssuedFallbackPanel

open DescentResetPublicOperandBook DescentResetOperandSetup
local notation "requestsAt" => DateInputs.RangeRequestsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom degreeAt capAt
local notation "cfg" => publicOperands (u).atlas (u).roots (u).menu.payload
local notation:max "K" batch:arg => publicOperandConfig B (setup).rotorBits (setup).queryBits M batch ((Z).unit/p)
    S.retainedNodes (S.retainedArgumentsAt G drift) p

local notation "dirs" => fun j : Fin (Fintype.card B.next.V)=>((Z).rawAtIndex T rank j).cast size

local notation "native" => (u).menu.publicData sh start count io.hubs g (2^n) (liveAt x₀) (regsAt x₀)
  values rfl x₀.val rh rg
local notation:max "printed" eqn:arg => Config.relabel eqn B.dimension.symm native
local notation:max "addr" eqn:arg => finProdFinEquiv (arg.cast (congrArg (fun c:Config=>c.args) eqn),
  node.cast (congrArg (fun c:Config=>c.nodes) eqn))

set_option hygiene true
theorem DateInputs.right_range_amount
    (prepared : (rc).PreparedFits book)
  (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
    (size:HH*rows=(setup).placement.sparse)
    (ready:(u).Ready) (archived:(r).Values) (μ:DescentGL.Layout (E).dim) (measured actors:Memory w)
    (requests:(requestsAt) ready archived μ measured actors)
    (x₀:Fin (v).receiver.blocks) (arg:Fin (r).args) (node:Fin (r).nodes)
    (rh:Fin (setup).placement.newHosts) (rg:Fin (setup).placement.groups)
    (values:(deck x₀).Values (setup).placement.newHosts (setup).placement.groups)
    (published:(u).PublicValuesRead ready actors (x₀.cast (u).operandBlocks) rfl dirs values)
    (small:2*(v).receiver.candidates<2^(v).receiver.queryBits)
    (choice:∀j:Fin 7,OrdinalRead u ready small actors ((v).operandOrdinal (u).operand j arg x₀ node))
    (live:0<(v).receiver.lanes) (bus:(u).operand.coeff*(v).receiver.lanes≤w)
    (lane:(v).receiver.signedBits*(v).receiver.lanes≤w)
    (batch:ℕ) (eqn:cfg=K batch) (boardAt:HEq (u).atlas.board (Z).graph)
    (axis:Fin 3) (amount:ℕ)
    («on»:(((K batch).oldConfig.header ((K batch).basic (printed eqn))) 0).val≠0)
    (tag:RightTrunkRank (Z).graph res (GroupStage.depthBound D n f g)
      ((((K batch).oldConfig.header ((K batch).basic (printed eqn))) 2).val))
    (surface:(K batch).column (Z).graph (setup).fieldBits (some (page axis)) (addr eqn) (printed eqn)=
      (amount:Cell (setup).fieldBits))
    (fits:amount<2^(setup).fieldBits) (received:amount<2^(v).receiver.valueBits) :
    ((choice (page axis)).amount rh rg).val=amount :=by
  obtain ⟨hdr,x,X,sig,geo,dim,sz,hub,fees,root,moved,mat,signed,controls,issued⟩:=requests
  let raw:=native
  have registers:=(Config.relay_relabel eqn B.dimension.symm (C:=(K batch).oldConfig) rfl raw).1
  have active : ((cfg).oldConfig.header ((cfg).basic raw) 0).val≠0:=fun gone=>«on» ((registers 0).trans gone)
  have shapeReg : ((cfg).reg raw 3).val=(((K batch).oldConfig.header ((K batch).basic (printed eqn))) 2).val :=
    (registers 2).symm
  have actual : RightTrunkRank (u).atlas.board (v).middle.rootDepth (u).roots.Ht ((cfg).reg raw 3).val :=by
    rw [shapeReg]
    refine RightTrunkRank.transport B.dimension.symm rfl boardAt (by change k = B.reset.k - B.terminals.commonDepth; rw [B.keyWidth, B.commonDepth]; omega) ?_ tag
    change GroupStage.depthBound venue.degree n f g=GroupStage.depthBound D n f g
    rw [degreeAt]
  obtain ⟨shape,mark,key,kind⟩:=actual
  have word:=issued x₀ arg node values published small choice live bus lane axis rh rg
  let strips:(r).Strips:=fun j=>blockValues geo.cut ((r).before geo.size archived j) (cast (congrArg DescentGL.Layout dim) μ)
  have clean:=(u).menu.relay_span_value dirs ((setup).assignedDigits geo.host geo.groups (u).bank.which X strips)
    ((r).outputID 1 (page axis) arg node) (x₀.cast (u).operandBlocks) rh rg raw (finProdFinEquiv (arg,node))
    (page axis) (published.2.2.2.2.2.1 rh rg) (published.2.2.2.2.2.2 rh rg) shape active mark kind
  have lifted:=Config.column_relabel eqn B.dimension.symm rfl boardAt raw arg node (setup).fieldBits (some (page axis))
  have column := lifted.symm.trans surface
  have decoded := clean.trans column
  have digit := (congrArg Fin.val decoded).trans (Fin.val_cast_of_lt fits)
  exact word.trans ((congrArg (fun x : ℕ => (x : Cell (v).receiver.valueBits).val) digit).trans
    (Fin.val_cast_of_lt received))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
