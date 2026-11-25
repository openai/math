import OAI.Hierarchy.DescentScheduledLaneReset
import OAI.Hierarchy.DescentPackedResetRotorRoles
import OAI.Hierarchy.DescentResetRootWord
import OAI.Hierarchy.DescentResetActorCalendar
import OAI.Hierarchy.DescentNamedResetSheets
import OAI.Hierarchy.DescentResetRetainedCalendar
import OAI.Hierarchy.DescentNamedResetVenue
import OAI.Hierarchy.DescentPhysicalResetReceipt
import OAI.Hierarchy.DescentResetCanvasIngress
import OAI.Hierarchy.DescentResetOperandSetupChart
import OAI.Hierarchy.DescentDatedReturnMetadata

namespace OAI
/-! # The issued reset address map at a public date of the original cap calendar -/
namespace Hierarchy.DescentDatedAddressBook
open DescentCompiler DescentSixParty DescentResetLocalRoster ProtocolRAM
noncomputable section

namespace ResetOutput

/-- The three incoming shape parameters describe the permanent field banks actually
issued by the preceding date. The first date can therefore consume the seed's one
node, and later dates use the padded capacity from the operand calendar. -/
structure Prior where
  venue : StageVenueTail.Date
  nodes : ℕ
  «arguments» : ℕ
  operandLanes : ℕ
  primitiveLanes : ℕ
  printedBits : ℕ

variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet : ℕ) (old : Prior)

def fromBoard (base : ℕ) : ResetOutput :=
  let calendar:=capCalendar G.b S.rounds g S.height
  let D:=old.venue.degree
  let cap:=(calendar.take age).prod*256
  let Ht:=GroupStage.depthBound D n f g
  let middle:=ResetMiddle.fromCalendar S k tail age p f D payload e previous n Ht calendar
  let actor:=ActorSetup.fromCalendar board S k tail age D e Ht
  let front:=CandidateFront.menu S board k tail age D f g (2^e) M C packet calendar
  let sheets:=CandidateSheets.fromBoard S board k tail age D f g cap M
  let nodes:=S.retainedNodes
  let args:=S.retainedArgumentsAt G drift
  let s:=DescentOperandWidth.recordBits G S k tail drift degree p
  let original:=originalBits D k n Ht cap (programCount board Ht) g
  let q:=Nat.clog 2 (2*sheets.candidates+1)
  let o : PublicOutput:=
    ⟨2^k,2^g*cap,sheets.metaBits,M,sheets.hosts,sheets.groups,sheets.candidates,q,s,
      ((7*args)*sheets.blocks)*nodes⟩
  let r:=S.retainedFromPrevious G k tail drift degree p age payload old.nodes old.arguments old.operandLanes
  let place:=DescentSixParty.AtomSchedule.retainedPlacementCalendar S board k age Ht M
  let selectors:=2^k*Nat.clog 2 (2^k+1)
  let roleUnit:=max 1 (max ((old.printedBits*(2*nodes+1)+old.printedBits)*2^k)
    (old.printedBits*2^k+selectors))
  let roleCut:=DescentPackedWalsh.laneBits r.cut payload roleUnit
  let previousRoles : DescentResetRetainedSetup.Layout:=
    { r with
      bits := old.printedBits
      previousArgs := 0
      args := 0
      previousLanes := old.primitiveLanes
      gatherLanes := 2^roleCut
      high := r.cut-roleCut
      low := roleCut+k
      decodedLanes := 2^roleCut
      emitLanes := 2^roleCut }
  let movement : DescentRetainedPrimitive.Layout:=
    ⟨previousRoles,sheets.hosts,place.shapes,sheets.groups,sheets.blocks,M⟩
  let lower:=actor.directoryEnd (middle.stop base)
  let pulls : DescentOperandRootPull.Pair:=
    ⟨middle.rootHeader (middle.afterProjection base),(front.parent lower).base,
      middle.rootHosts,sheets.hosts,sheets.groups,sheets.blocks,middle.rootField,middle.rootLanes,
      M,D,cap,k,n⟩
  let groupDigits:=ResetInput.calendarLanes S G.b (age+1)
  let batches:=DescentRecordedRotorLayers.layers n packet f cap*groupDigits
  let readBits:=max s (max 1 (max middle.signedBits sheets.metaBits))
  let roleBits:=max readBits (max q (max middle.rootField front.privateBits))
  let setup : DescentResetOperandSetup.Chart:=
    {retained:=r,placement:=place,packets:=pulls,
     publicCasts:=⟨middle.rootField,sheets.stemBits,sheets.metaBits,roleBits,M⟩,oldDegree:=D,oldCap:=cap,
     oldPieces:=groupDigits,signedBits:=middle.rootField,signedLanes:=middle.rootLanes,
     ticketBits:=sheets.metaBits,fieldBits:=readBits,queryBits:=q,rotorBits:=roleBits,
     fallbackBits:=roleBits,fallbackInputs:=8+12*(2^k*(2*cap))+
       DescentFallbackPeriod.inputCount D (2^k) cap n k+((2^k)*(2^k)+D*(D*6))}
  let venue:=ResetVenue.fromBoard board old.venue middle actor o f g nextM
  { middle:=middle, actor:=actor, front:=front, sheets:=sheets, receiver:=o,
    setup:=setup, funded:=DescentNamedFundedChart.setup old.venue middle, venue:=venue,
    roleTransfer:=⟨movement,D,cap,middle.rootField,middle.rootLanes⟩,
    birth:=⟨place,k,n,nodes,args,DescentPackedResetRotorRoles.roleBits n,batches,middle.rootLanes,
      Nat.clog 2 (6+2*(2^k*2^n)),old.venue.paidBits,s⟩,
    primitive:=⟨⟨sheets.blocks,nodes,sheets.hosts,sheets.groups,old.printedBits,M⟩,DescentPackedResetRotorRoles.roleBits n⟩,
    metadata:=⟨⟨sheets.blocks,nodes,sheets.hosts,sheets.groups,s,M⟩,old.venue.paidBits,s⟩,
    ticketBits:=original, assemblerBits:=sheets.metaBits, nodes:=nodes,
    argumentSlots:=args, nodeBits:=s,
    rootOutputBits:=ResetMiddle.rootWord board k Ht f cap C packet (DescentPackedResetRotorRoles.roleBits n) batches }

local notation "out" => fromBoard G S board k tail age p f g drift degree payload e previous M nextM C packet old

theorem shape (base : ℕ) : (out base).receiver.candidates=(out base).sheets.candidates ∧
    (out base).receiver.signedBits=(out base).assemblerBits ∧
    (out base).receiver.fields=((7*(out base).argumentSlots)*(out base).receiver.blocks)*(out base).nodes ∧
    (out base).setup.retained.previousNodes=old.nodes ∧
    (out base).setup.retained.previousArgs=old.arguments ∧
    (out base).metadata.chart.nodes=(out base).nodes :=⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end ResetOutput
end
end Hierarchy.DescentDatedAddressBook

namespace Hierarchy.DescentDatedAddressBook
open DescentSixParty DescentCompiler ProtocolRAM
noncomputable section

/-- Birth has one node and three flattened argument rows per initial interval.
Every later date publishes the uniform bounded archives. -/
def ResetOutput.Prior.atDate {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)
    (age p drift oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date) : ResetOutput.Prior :=
  ⟨venue,if age=0 then 1 else S.retainedNodes,
    if age=0 then 3*(S.firstWidth G.b p/p) else S.retainedArgumentsAt G drift,oldLanes,primitiveLanes,printedBits⟩

namespace PhysicalReset
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
    (addr : ℕ→ℕ→Bank) (roster : Bank)

local notation "prior₀" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "out₀" => ResetOutput.fromBoard G S board k tail age p f g drift degree payload e previous M nextM C packet prior₀

private def buildAt (source : ℕ→ℕ→Bank) (base : ℕ) : PhysicalReset :=
  let out := out₀ base
  fromCalendar S k tail age G.b p f venue.degree payload e out.middle.stencil.n out.middle.stencil.t
    (capCalendar G.b S.rounds g S.height) source roster out

local notation "build₀" => buildAt G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue roster

private theorem buildAt_successor (source : ℕ→ℕ→Bank) (base : ℕ) :
    (build₀ source base).successor = out₀ base := rfl

private theorem buildAt_stage (source : ℕ→ℕ→Bank) (floor base : ℕ) :
    (build₀ source base).stageStart floor = (build₀ source 0).stageStart floor := by
  dsimp only [stageStart, buildAt, fromCalendar, ResetOutput.fromBoard]

private theorem buildAt_rebased (source : ℕ→ℕ→Bank) (floor base : ℕ) :
    (build₀ source base).rebased floor = (build₀ source 0).rebased floor := by
  dsimp only [rebased, chart, buildAt, fromCalendar]

private theorem buildAt_floor (source : ℕ→ℕ→Bank) (floor base : ℕ) :
    (build₀ source base).rebased ((build₀ source base).stageStart floor) =
      (build₀ source 0).rebased ((build₀ source 0).stageStart floor) := by
  rw [buildAt_stage (base := base), buildAt_rebased (base := base)]

private theorem final_successor (source : ℕ→ℕ→Bank) (floor : ℕ) :
    let entered := build₀ source 0
    let date := build₀ source (entered.rebased (entered.stageStart floor))
    date.successor = out₀ (date.rebased (date.stageStart floor)) := by
  let base := (build₀ source 0).rebased ((build₀ source 0).stageStart floor)
  exact (buildAt_successor G S board k tail age p f g drift degree payload e previous M nextM C packet oldLanes primitiveLanes printedBits venue roster source base).trans
    (congrArg (out₀) (buildAt_floor G S board k tail age p f g drift degree payload e previous M nextM C packet oldLanes primitiveLanes printedBits venue roster source floor base).symm)

/-- First run the public address calculation up to the end of the basis change. Both
original root packets and the parent directory can then be named by an absolute address. -/
def named (floor : ℕ) : PhysicalReset :=
  let «prefix» := build₀ addr 0
  let L:=«prefix».ingress
  let read (x j : ℕ):=if hx:x<2^L.k then
      if hj:j<2*L.cap then L.tokens floor (⟨x,hx⟩,⟨j,hj⟩) else addr x j
    else addr x j
  let entered := build₀ read 0
  build₀ read (entered.rebased (entered.stageStart floor))

local notation "date₀" => named G S board k tail age p f g drift degree payload e previous M nextM C packet oldLanes primitiveLanes printedBits venue addr roster

theorem named_successor (floor : ℕ) :
    (date₀ floor).successor=out₀ ((date₀ floor).rebased ((date₀ floor).stageStart floor)) := by
  unfold named
  apply final_successor

theorem named_repacking (floor : ℕ) :
    (date₀ floor).fullEnd floor=(out₀ ((date₀ floor).rebased ((date₀ floor).stageStart floor))).metadataEnd
      ((date₀ floor).rebased ((date₀ floor).stageStart floor)) := by
  unfold fullEnd endAddress
  rw [named_successor]

end PhysicalReset
end
end Hierarchy.DescentDatedAddressBook

end OAI
