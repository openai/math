import OAI.Computability.VPVNP.LiveFirstTailOutput
import OAI.Computability.VPVNP.LiveOutsideTailCount

/-!
# Counting the first evaluator transition after midpoint initialization

The first router writes the initial control word. The deterministic midpoint
preparation returns at the last router. Removing both prefixes from the
accepting paths retains their actual reports in the bucket cap.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorRoutes

open BurstRAM PairStages LiveEvaluatorEncoding LiveEvaluatorRAM
open OutsideTraces OutsideTailStages OutsideTailCount
open scoped Fin.CommRing

variable (G : Group)

/-- Count after the native preparation, charging every initialization burst
to the same global cap as the eventual transition. -/
theorem countAfterInitialization {S H h Δ M n cost preCost : ℕ}
    (layout : LiveEvaluatorTail.Layout G.evaluator.extra M G.w Δ)
    (init : Code G.evaluator.extra M) (bits : LiveChain.TailBits h Δ)
    (i : Fin (2^h)) (first : i.val = 0) (m final : Memory G.w)
    (fit : GeometryFit G M) (start : G.tagged Stage.firstTail m)
    (flag : m ((Router.firstTail.data G.g G.lit) 0).val = 1)
    (run : Advice.Returning G.P G.clock n 22 (putMemory G false m) final)
    (work : Advice.CostLimit G.P G.clock n (putMemory G false m) cost)
    (config : ConfigAt final (G.transitionPub 1) init) (tag : G.tagged Stage.last final)
    (o : Output G final (LiveEvaluatorTail.boundary layout init bits i.succ))
    (pre : List (Report G.w)) (hr : Resources pre preCost 11 G.clock)
    (hcall : callBound G.w ≤ H)
    (budget : preCost+8+cost+routeCost G.w M+transitionCost M ≤ S*H) :
    Nat.card (ActualPaths G.P G.clock 0 m (fun rs => withinCaps S H (pre++rs))) =
      ChainAssignments.tailCount G.evaluator layout init bits i := by
  obtain ⟨rs,exec,ends,mem,_,bound⟩ := run
  have hres : Resources rs cost 23 G.clock :=
    ⟨work _ exec, fun r h => by have := (bound r h).1; omega,
      fun r h => by have := (bound r h).2; omega⟩
  have old (c : Code G.evaluator.extra M) : LiveEvaluatorTail.boundary layout init bits i.castSucc = some c ↔
      ConfigAt final (G.transitionPub 1) c := by
    have hz : i.castSucc = 0 := Fin.ext first
    rw [hz,LiveEvaluatorTail.boundary_zero,Option.some.injEq,eq_comm]
    exact (configAt_eq_iff G fit.prep.width fit.prep.states config c).symm
  have allRes := (hr.append (putRoute G false)).append hres
  have counted := lastCount_capped G layout init bits i final fit tag old o _ allRes
    (by unfold callBound at hcall ⊢; omega) budget
  have hclk := fit.gatherClock
  rw [Nat.card_congr (putHandoff G false fit.prep.width (by omega) m start flag _).symm]
  let cap := fun xs => withinCaps S H (pre++(putLogs G false++xs))
  have e := emptySegmentEquiv exec cap
  rw [ends,mem] at e
  rw [Nat.card_congr e.symm]
  simpa only [cap,List.append_assoc] using counted

end LiveProgram.EvaluatorRoutes

end VPVNP
end Computability
end OAI
