import OAI.Computability.VPVNP.LiveOutsideTailStages
import OAI.Computability.VPVNP.LiveLinkedEvaluatorRouteCost

/-! # Applying the actual outside-stage budgets to the tail path count

The cost of the completed prefix is charged before counting the transition.
The gathered bit words and the endpoint sentinel have their canonical linked
logs. Thus a single numerical budget suffices for all paths of a noninitial
group, including groups whose cut fields decode to malformed configurations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.OutsideTailCount

open BurstRAM LiveStageLink PairStages LiveEvaluatorEncoding LiveEvaluatorRAM LiveConfigGather
open LiveEvaluatorRAM.Schedule (calls)
open EvaluatorRoutes OutsideTraces OutsideTailStages
open scoped Fin.CommRing

variable (G : PairStages.Group) {M : ℕ}

/-- A common bound for either exit of the last router. -/
def routeCost (w M : ℕ) := 4+fieldWords M*(w+4)

/-- The cost allowance for transition preparation and all cell checks, including a dispatch
charge for every call. -/
def transitionCost (M : ℕ) := (10+7*(2*(2*M+1)))+calls M

theorem output_resources {m : Memory G.w} {b : Option (Code G.evaluator.extra M)} (o : Output G m b) :
    Resources o.logs (routeCost G.w M) (G.w+4) (instructionBound G) := by
  refine ⟨o.logs_cost,o.logs_calls,?_⟩
  cases o with
  | cut _ bits => exact (gatherRoute G true bits).work
  | final => exact (putRoute G true).work

/-- Count starting at the last router, from an already accounted prefix. -/
theorem lastCount_capped {h Δ S H : ℕ} (layout : LiveEvaluatorTail.Layout G.evaluator.extra M G.w Δ)
    (init : Code G.evaluator.extra M) (bits : LiveChain.TailBits h Δ) (i : Fin (2^h)) (m : Memory G.w)
    (fit : GeometryFit G M) (tag : G.tagged Stage.last m)
    (incoming : ∀ c, LiveEvaluatorTail.boundary layout init bits i.castSucc = some c ↔ ConfigAt m (G.transitionPub 1) c)
    (o : Output G m (LiveEvaluatorTail.boundary layout init bits i.succ))
    (pre : List (Report G.w)) {a b instr : ℕ} (hr : Resources pre a b instr)
    (hcall : max b (max 11 (G.w+4)) ≤ H) (budget : a+routeCost G.w M+transitionCost M ≤ S*H) :
    Nat.card (ActualPaths G.P G.clock 0 m (fun rs => withinCaps S H (pre++rs))) =
      ChainAssignments.tailCount G.evaluator layout init bits i := by
  have hrs := hr.append (output_resources G o)
  apply lastCount G layout init bits i m fit tag incoming o pre
  · omega
  · intro r hm; have hp := hrs.calls r hm; omega
  · have hc := hrs.cost
    unfold transitionCost at budget
    omega

/-- Count from the first router of every noninitial tail group. The
incoming gather, outgoing route, and complete linked transition fit the
same cap chosen before the choices of that transition. -/
theorem nonfirstCount_capped {h Δ S H : ℕ} (layout : LiveEvaluatorTail.Layout G.evaluator.extra M G.w Δ)
    (init : Code G.evaluator.extra M) (bits : LiveChain.TailBits h Δ) (i : Fin (2^h)) (m : Memory G.w)
    (fit : GeometryFit G M) (tag : G.tagged Stage.firstTail m) (flag : m ((Router.firstTail.data G.g G.lit) 0).val = 0)
    (F : EvaluatorGather.Fit G false (fieldWords M)) (raw : Fin (fieldWords M*G.w) → Bool)
    (image : ArrayBitImage m (EvaluatorGather.operands G false 0) raw)
    (fresh : G.addr.val < (EvaluatorGather.operands G false 0).val ∨
      (EvaluatorGather.operands G false 0).val+fieldWords M*G.w ≤ G.addr.val)
    (value : LiveEvaluatorTail.boundary layout init bits i.castSucc = (format F.width fit.prep.states).decode raw)
    (o : Output G (gatherMemory G false F m raw) (LiveEvaluatorTail.boundary layout init bits i.succ))
    (pre : List (Report G.w)) {a b instr : ℕ} (hr : Resources pre a b instr)
    (hcall : max b (max 11 (G.w+4)) ≤ H) (budget : a+2*routeCost G.w M+transitionCost M ≤ S*H) :
    Nat.card (ActualPaths G.P G.clock 0 m (fun rs => withinCaps S H (pre++rs))) =
      ChainAssignments.tailCount G.evaluator layout init bits i := by
  have hi : Resources (gatherLogs G false raw) (routeCost G.w M) (G.w+4) (instructionBound G) :=
    ⟨gatherLogs_cost G false raw,gatherLogs_calls G false raw,(gatherRoute G false raw).work⟩
  have hrs := (hr.append hi).append (output_resources G o)
  apply nonfirstCount G layout init bits i m fit tag flag F raw image fresh value o pre
  · omega
  · intro r hm; have hp := hrs.calls r hm; omega
  · have hc := hrs.cost
    unfold transitionCost at budget
    omega

end LiveProgram.OutsideTailCount

end VPVNP
end Computability
end OAI
