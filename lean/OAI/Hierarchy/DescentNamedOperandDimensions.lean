import OAI.Hierarchy.DescentNamedPublicSocketConfig

namespace OAI
/-! # Dimensions of the two original operand words at a named reset -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 290000
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl}
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
local notation "control" => (v).controlRegisters
local notation "first_" => (v).controlFloor base₀
local notation "actor" => (v).actor
local notation "stage_" x:arg => (control).live first_ (x:DescentColonies.Block k).val
local notation "regs_" x:arg => (control).ports first_ ((a).c/2) (x:DescentColonies.Block k).val ((actor).directory actorBase).inverse
  ((actor).depths actorBase) ((actor).levels actorBase)
local notation "deck" x:arg => OperandMenu.publicPorts («a»:=a) sh start count io.hubs g (2^n) (stage_ x) (regs_ x)
local notation "cfg" => publicOperands (u).atlas (u).roots (u).menu.payload
local notation "remaining" => (Z).k-(T).commonDepth

/-- Physical dimensions shared by the old packet, operand menu and both issued root stages. -/
structure DateInputs.OperandDimensions (format₀ : DescentResetPublicOperandBook.Config)
    (ports : DescentResetPublicOperandBook.Ports) (rootField rotorN measuredDegree measuredCap rotorDim radius : ℕ) : Prop where
  oldDegree : format₀.oldDegree=measuredDegree
  donors : format₀.donors=2^radius
  oldCap : format₀.oldCap=measuredCap
  rotorBits : rotorN=rotorDim
  residual : format₀.residual=radius
  oldBits : ports.packets.oldBits=rootField
  width : rootField≤ports.casts.bits
  fieldBits : format₀.fieldBits=ports.casts.bits
  castWidth : ports.casts.width 0=rootField
  fallFields : (ports.packets.stage 0 false).fields=DescentFallbackPeriod.inputCount measuredDegree (2^radius) measuredCap rotorDim radius
  matrixFields : (ports.packets.stage 0 true).fields=DescentRotorWindowArchive.count measuredDegree (2^radius) measuredCap

/-- The real named actuator casts every earlier root field into the role word.
The two packet stages retain the full fallback packet and directed rotor matrix. -/
theorem DateInputs.named_operand_dimensions (degreeAt : venue.degree=D)
    (capAt : input.placement.cap=cap) (x : DescentColonies.Block k) :
    DateInputs.OperandDimensions (cfg) (deck x) (v).middle.rootField (v).middle.rotorBits
      input.placement.degree input.placement.cap (Z).n remaining :=by
  have deg : venue.degree=input.placement.degree:=degreeAt.trans input.branch.symm
  have span : remaining=k:=ClosedReset.Window.funded_residual B
  have half : 2*cap/2=cap:=by omega
  refine ⟨deg,?_,?_,B.dimension.symm,span.symm,rfl,?_,rfl,rfl,?_,?_⟩
  · change 2^k=2^remaining
    rw [span]
  · change 2*cap/2=input.placement.cap
    exact half.trans capAt.symm
  · change (v).middle.rootField≤ max _ (max _ (max (v).middle.rootField _))
    exact (Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  · change DescentFallbackPeriod.inputCount venue.degree (2^k) cap n k=_
    rw [deg,span,capAt,B.dimension]
  · change DescentRotorWindowArchive.count venue.degree (2^k) cap=_
    rw [deg,span,capAt]

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
