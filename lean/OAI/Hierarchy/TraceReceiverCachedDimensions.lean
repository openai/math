import OAI.Hierarchy.TraceReceiverRegisteredGeometry
import OAI.ThreeFlat.RAM.HistoryNodeValue
import OAI.ThreeFlat.RAM.TickTerminalRoot

namespace OAI
/-! # Dimensions read from an authentic cache of the issued physical factor -/

noncomputable section
namespace Hierarchy.GridRegisteredSetting.RunData
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open TraceDistribution TraceFactorReceiver.Gather RAM Computability.VPVNP.BurstRAM PrivateRAM Filter
open scoped BigOperators Classical

variable {F : Type} [Field F] [Fintype F] {W pc regs words S base fuel axes low : ℕ}

omit [Field F] [Fintype F] in
private theorem cells_heq {p q : ℕ} (a : BitNetwork F p) (b : BitNetwork F q)
    (arity : p=q) (same : HEq a b) : a.cells=b.cells := by
  subst q
  rw [eq_of_heq same]

theorem cached_dimensions_pay (D : RunData F W pc regs words S base fuel axes low)
    (h : D.run.plan.History) (i : Fin (D.roots h)) (w degree stageRate rootRate : ℕ)
    (v : HistoryStageBody.Physical.NodeValue F) (arity : v.pins=D.issuedPorts h i)
    (net : HEq v.net (D.issuedTree h i).compile)
    (paid : D.issuedTreeWork h degree stageRate rootRate i≤
      D.work h D.issuedCharges (D.issuedUnit w degree stageRate rootRate) i) :
    v.net.cells+v.net.internal+v.pins≤D.work h D.issuedCharges (D.issuedUnit w degree stageRate rootRate) i := by
  have hidden {p q : ℕ} (a : BitNetwork F p) (b : BitNetwork F q) (eqn : p=q) (same : HEq a b) :
      a.internal=b.internal := by subst q; rw [eq_of_heq same]
  rw [cells_heq v.net _ arity net,hidden v.net _ arity net,arity]
  exact D.issued_dimensions_pay h i w degree stageRate rootRate paid

/-- The emitted result header gives both remaining root-task dimensions at the chosen rank. -/
theorem issued_cache_fields (D : RunData F W pc regs words S base fuel axes low) (h : D.run.plan.History)
    (i : Fin (D.roots h)) (arena : TickTerminalRoot.Arena) (age node : ℕ) (m : Memory W)
    (tag : ((Fin 3→Bool)→F)→ℕ) (v : HistoryStageBody.Physical.NodeValue F) (cache : v.Cached tag age node m)
    (results : arena.results=TickWorkspace.base age 13) (select : TickTerminalRoot.rootId arena (fun a=>(m a).val)=node)
    (arity : v.pins=D.issuedPorts h i) (net : HEq v.net (D.issuedTree h i).compile) :
    let task:=TickTerminalRoot.terminal arena (fun a=>(m a).val)
    task.rows=(D.issuedTree h i).compile.cells ∧ task.localPins=D.issuedPorts h i := by
  have hdr : HistoryStageRoot.atResult (fun a=>(m a).val)
      (arena.results+8*TickTerminalRoot.rootId arena (fun a=>(m a).val))=v.info := by
    rw [results,select]
    exact cache.header
  exact ⟨(congrArg HistoryStageRoot.Result.rows hdr).trans (cells_heq v.net _ arity net),
    (congrArg HistoryStageRoot.Result.pins hdr).trans arity⟩

end Hierarchy.GridRegisteredSetting.RunData
end

end OAI
