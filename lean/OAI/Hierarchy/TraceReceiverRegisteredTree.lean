import OAI.Hierarchy.TraceReceiverRegisteredClock
import OAI.Hierarchy.TraceReceiverJointRoot
import OAI.Hierarchy.TraceReceiverCachedDimensions

namespace OAI
/-! # Joint terminal bill from the actual decoded selected native root -/

noncomputable section
namespace Hierarchy.GridRegisteredSetting.RunData
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open TraceDistribution TraceFactorReceiver.Gather RAM Computability.VPVNP.BurstRAM PrivateRAM Filter
open scoped BigOperators Classical

variable {F : Type} [Field F] [Fintype F] {W pc regs words S base fuel axes low : ℕ}

/-- All costs in a terminal root visit use the same S43 work word at the actual
final ordinal. The remaining half sizes and row count refer to the decoded root task. -/
theorem joint_root_at {w levels degree : ℕ} (D : RunData F (64*w) pc regs words S base fuel axes low)
    (h : D.run.plan.History) (i : Fin (D.roots h)) (A : TickTerminalRoot.Arena)
    (task : HistoryTerminalTape.Root) (raw : ℕ→ℕ) (pairs : ℕ)
    (large : max 64 D.block.stageClockRate≤w) (count : levels≤w)
    (resources : (D.issuedTree h i).resources≤Run.treeFee (D.block.localCoefficient*(64*w+1)^3)
        (D.block.repeat D.passes).length*D.rawCharge h i)
    (deg : task.halves≤degree) (paired : task.ext≤2*pairs)
    (mass : 1+(∑ j : Fin task.halves,(HistoryTerminalTape.half task raw j.val).width)+pairs≤D.rawCharge h i)
    (rows : task.rows=(D.issuedTree h i).compile.cells) (pins : task.localPins=D.issuedPorts h i) :
    let B:=D.block
    let T:=D.issuedTree h i
    let stages:=(B.repeat D.passes).length
    let fee:=B.nativeVisitFee levels (B.localCoefficient*(64*w+1)^3) (D.run.endLevel h 0)
    let setup:=setupPrice stages B.stageClockRate
    fee*D.rawCharge h i+(T.replayWork setup+
        (7224+19+1016*T.compile.cells+(9+5*T.compile.internal+22*T.compile.cells))+
        TickTerminalRoot.oneCost (64*w) A task raw)+(perRoot+22*task.localPins) ≤
      D.work h D.issuedCharges (D.issuedUnit w degree (fullRate B.stageClockRate 0)
        TickTerminalRoot.rootFactor) i :=
  D.joint_root_at_rate h i D.block.stageClockRate A task raw pairs large count resources deg paired mass rows pins

/-- The once-charged actual operations at an authenticated S13 result and its emitted
half records. All numerical task metadata is read from those two native tables. -/
theorem joint_root_from_cache {w levels : ℕ} (D : RunData F (64*w) pc regs words S base fuel axes low)
    (h : D.run.plan.History) (i : Fin (D.roots h)) (arena : TickTerminalRoot.Arena)
    (age node suffix : ℕ) (m : Memory (64*w)) (tag : ((Fin 3→Bool)→F)→ℕ) (v : HistoryStageBody.Physical.NodeValue F)
    (cache : v.Cached tag age node m) (results : arena.results=TickWorkspace.base age 13)
    (select : TickTerminalRoot.rootId arena (fun a=>(m a).val)=node)
    (arity : v.pins=D.issuedPorts h i) (net : HEq v.net (D.issuedTree h i).compile)
    (tab : TraceReceiverTerminalMap.HalfRows (D.run.terminalLayer h).state (D.terminalWords h)
      (D.terminalSite h i) (TickTerminalRoot.terminal arena (fun a=>(m a).val)) (fun a=>(m a).val) suffix)
    (even : Even S) (large : max 64 D.block.stageClockRate≤w) (count : levels≤w)
    (resources : (D.issuedTree h i).resources≤Run.treeFee (D.block.localCoefficient*(64*w+1)^3)
        (D.block.repeat D.passes).length*D.rawCharge h i) :
    let B:=D.block
    let T:=D.issuedTree h i
    let stages:=(B.repeat D.passes).length
    let raw:=fun a=>(m a).val
    let task:=TickTerminalRoot.terminal arena raw
    let fee:=B.nativeVisitFee levels (B.localCoefficient*(64*w+1)^3) (D.run.endLevel h 0)
    let setup:=setupPrice stages B.stageClockRate
    fee*D.rawCharge h i+(T.replayWork setup+
        (7224+19+1016*T.compile.cells+(9+5*T.compile.internal+22*T.compile.cells))+
        TickTerminalRoot.oneCost (64*w) arena task raw)+(perRoot+22*task.localPins) ≤
      D.work h D.issuedCharges (D.issuedUnit w (2*2^B.exponent 0) (fullRate B.stageClockRate 0)
        TickTerminalRoot.rootFactor) i :=
  D.joint_root_from_cache_at_rate h i D.block.stageClockRate arena age node suffix m tag v cache results
    select arity net tab even large count resources

end Hierarchy.GridRegisteredSetting.RunData
end

end OAI
