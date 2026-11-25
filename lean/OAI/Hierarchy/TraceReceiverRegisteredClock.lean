import OAI.Hierarchy.TraceReceiverRegisteredGeometry
import OAI.Hierarchy.TraceReceiverRootPrice
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
theorem joint_root_at_rate {w levels degree : ℕ} (D : RunData F (64*w) pc regs words S base fuel axes low)
    (h : D.run.plan.History) (i : Fin (D.roots h)) (rate : ℕ) (A : TickTerminalRoot.Arena)
    (task : HistoryTerminalTape.Root) (raw : ℕ→ℕ) (pairs : ℕ)
    (large : max 64 rate≤w) (count : levels≤w)
    (resources : (D.issuedTree h i).resources≤Run.treeFee (D.block.localCoefficient*(64*w+1)^3)
        (D.block.repeat D.passes).length*D.rawCharge h i)
    (deg : task.halves≤degree) (paired : task.ext≤2*pairs)
    (mass : 1+(∑ j : Fin task.halves,(HistoryTerminalTape.half task raw j.val).width)+pairs≤D.rawCharge h i)
    (rows : task.rows=(D.issuedTree h i).compile.cells) (pins : task.localPins=D.issuedPorts h i) :
    let B:=D.block
    let T:=D.issuedTree h i
    let stages:=(B.repeat D.passes).length
    let fee:=(D.run.endLevel h 0+1)*(rate*(B.localCoefficient*(64*w+1)^3)*(4*levels+4))
    let setup:=setupPrice stages rate
    fee*D.rawCharge h i+(T.replayWork setup+
        (7224+19+1016*T.compile.cells+(9+5*T.compile.internal+22*T.compile.cells))+
        TickTerminalRoot.oneCost (64*w) A task raw)+(perRoot+22*task.localPins) ≤
      D.work h D.issuedCharges (D.issuedUnit w degree (fullRate rate 0)
        TickTerminalRoot.rootFactor) i := by
  let T:=D.issuedTree h i
  have q:=D.issued_shape h
  have r : task.rows≤T.resources := by
    rw [rows,Tree.compiled_rows]
    change T.rows≤T.bits+T.rows+T.nodes+T.footprint.pins
    omega
  have terminal:=(TickTerminalRoot.work_bound (64*w) A task raw).trans
    (Nat.mul_le_mul_left TickTerminalRoot.rootFactor
      (TickTerminalRoot.charge_covers task raw deg paired mass (r.trans resources)))
  rw [←Nat.mul_assoc] at terminal
  dsimp only
  rw [pins]
  exact joint_root_rate rate D.block.localCoefficient (w:=w) (levels:=levels) (ended:=D.run.endLevel h 0)
    (stages:=(D.block.repeat D.passes).length) (depth:=4+(D.block.repeat D.passes).length)
    (degree:=degree) T (D.rawCharge h i) (D.issuedPorts h i) _ large count q.1.le (by omega)
    (q.2 i) (by unfold Block.localCoefficient; omega) (by omega) (D.issued_ports_pay h i)
    resources terminal

/-- The once-charged actual operations at an authenticated S13 result and its emitted
half records. All numerical task metadata is read from those two native tables. -/
theorem joint_root_from_cache_at_rate {w levels : ℕ} (D : RunData F (64*w) pc regs words S base fuel axes low)
    (h : D.run.plan.History) (i : Fin (D.roots h)) (rate : ℕ) (arena : TickTerminalRoot.Arena)
    (age node suffix : ℕ) (m : Memory (64*w)) (tag : ((Fin 3→Bool)→F)→ℕ) (v : HistoryStageBody.Physical.NodeValue F)
    (cache : v.Cached tag age node m) (results : arena.results=TickWorkspace.base age 13)
    (select : TickTerminalRoot.rootId arena (fun a=>(m a).val)=node)
    (arity : v.pins=D.issuedPorts h i) (net : HEq v.net (D.issuedTree h i).compile)
    (tab : TraceReceiverTerminalMap.HalfRows (D.run.terminalLayer h).state (D.terminalWords h)
      (D.terminalSite h i) (TickTerminalRoot.terminal arena (fun a=>(m a).val)) (fun a=>(m a).val) suffix)
    (even : Even S) (large : max 64 rate≤w) (count : levels≤w)
    (resources : (D.issuedTree h i).resources≤Run.treeFee (D.block.localCoefficient*(64*w+1)^3)
        (D.block.repeat D.passes).length*D.rawCharge h i) :
    let B:=D.block
    let T:=D.issuedTree h i
    let stages:=(B.repeat D.passes).length
    let raw:=fun a=>(m a).val
    let task:=TickTerminalRoot.terminal arena raw
    let fee:=(D.run.endLevel h 0+1)*(rate*(B.localCoefficient*(64*w+1)^3)*(4*levels+4))
    let setup:=setupPrice stages rate
    fee*D.rawCharge h i+(T.replayWork setup+
        (7224+19+1016*T.compile.cells+(9+5*T.compile.internal+22*T.compile.cells))+
        TickTerminalRoot.oneCost (64*w) arena task raw)+(perRoot+22*task.localPins) ≤
      D.work h D.issuedCharges (D.issuedUnit w (2*2^B.exponent 0) (fullRate rate 0)
        TickTerminalRoot.rootFactor) i := by
  have dims:=D.issued_cache_fields h i arena age node m tag v cache results select arity net
  have fields:=D.issued_task_fields h i _ _ suffix tab even
  exact D.joint_root_at_rate h i rate arena _ _ (D.terminalPairs h i) large count resources fields.1.le
    fields.2.1.le fields.2.2.1 dims.1 dims.2

end Hierarchy.GridRegisteredSetting.RunData
end

end OAI
