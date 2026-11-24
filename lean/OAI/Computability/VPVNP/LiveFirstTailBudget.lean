import OAI.Computability.VPVNP.LiveOutsideTailCount
import OAI.Computability.VPVNP.LiveOutsideAllCaps
import OAI.Computability.VPVNP.LiveLinkedEvaluatorGeometry
import OAI.Computability.VPVNP.LiveProgramHeader

/-!
# The transcript budget of the initialized first tail group

The first nonempty evaluator group executes the header, both routers, the
initial state writer, the packing and input stages, and one terminal
transition. The outgoing gather allowance also pays for the last sentinel
when this is the only tail group. The common outside-work bound therefore
provides the budget for every accepting continuation from the midpoint.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.FirstTailBudget

open PairStages LiveEvaluatorTailCost OutsideTailStages OutsideTailCount
open Filter CursorBounds CursorNetwork

/-- The specific amount charged by the post-initialization count theorem,
including the header and mode router. -/
def cost (G : Group) (raw : ℕ) : ℕ :=
  LiveHeaderSchedule.costBound (Header.sizes G.constants G.g)+4+8+
    packWork (params G raw)+inputWork (params G raw)+
    routeCost G.w (EvaluatorRoutes.radius G)+transitionCost (EvaluatorRoutes.radius G)

private theorem group_cost (u : Parameters) :
    8+packWork u+inputWork u+routeCost u.wordWidth u.radius+transitionCost u.radius ≤
      groupBound u true false false := by
  have hwords : LiveEvaluatorEncoding.fieldWords u.radius = u.configWords := by
    unfold LiveEvaluatorEncoding.fieldWords Parameters.configWords; omega
  have hroute : routeCost u.wordWidth u.radius = 4+(u.wordWidth+4)*u.configWords := by
    rw [routeCost, hwords, Nat.mul_comm]
  have htrans : transitionCost u.radius = u.transitionCost+u.configWords := by
    unfold transitionCost Parameters.transitionCost Parameters.configWords LiveEvaluatorRAM.Schedule.calls
    omega
  rw [hroute, htrans, ← groupBudget]
  simp only [firstBudget, lastBudget, ite_true, Bool.false_eq_true, ite_false]
  omega

/-- The physical route budget is covered by the common outside-work bound
with the ordinary outgoing-gather allowance. -/
theorem cost_le_actualBound (G : Group) (raw : ℕ) :
    cost G raw ≤ OutsideBudget.actualBound G.constants G.g raw true false false := by
  have h := group_cost (params G raw)
  change 8 + packWork (params G raw) + inputWork (params G raw) +
    routeCost G.w (EvaluatorRoutes.radius G) + transitionCost (EvaluatorRoutes.radius G) ≤ _ at h
  unfold cost OutsideBudget.actualBound
  dsimp only
  change LiveHeaderSchedule.costBound (Header.sizes G.constants G.g)+4+8+
    packWork (params G raw)+inputWork (params G raw)+routeCost G.w (EvaluatorRoutes.radius G)+
    transitionCost (EvaluatorRoutes.radius G) ≤ LiveHeaderSchedule.costBound (Header.sizes G.constants G.g)+
    8+4*(G.constants.labels.eval G.g+1)+100+16*(OutsideBudget.auxWords (Header.sizes G.constants G.g)
      (G.constants.labels.eval G.g)+1)+7*(G.constants.labels.eval G.g*G.constants.Z.eval G.g+1)+
    groupBound (params G raw) true false false
  omega

/-- The site exponent is chosen before the length threshold. For every
bounded advice prefix, the ordinary per-call cap and the full initialized
group budget then hold simultaneously. -/
theorem eventually_countCaps {C : ℕ} (u : PairExponents C) (c : Constants) (E : UniversalMachine.Program) :
    ∃ B₀, ∀ B ≥ B₀, ∀ᶠ n : ℕ in atTop, ∀ G : Group,
      G.g = paperGeometry B (liveCapacity u) n → G.constants = c → G.evaluator = E →
      ∀ raw, raw ≤ G.constants.prefixCapacity.eval G.g →
        cost G raw ≤ processorCount B n*G.g.H ∧ OutsideTailStages.callBound G.w ≤ G.g.H := by
  obtain ⟨B₀, h⟩ := OutsideTraces.eventually_all_caps u c E
  refine ⟨B₀, fun B hB => ?_⟩
  filter_upwards [h B hB] with n hn G hg hc he raw hraw
  obtain ⟨hcost, hcap, _⟩ := hn G hg hc he raw true false false hraw
  have hpos : 0 < G.g.H := (by decide : 0 < 26).trans_le ((le_max_left ..).trans hcap)
  exact ⟨(cost_le_actualBound G raw).trans (hcost.le.trans (Nat.le_mul_of_pos_right _ hpos)),
    (le_max_right ..).trans hcap⟩

end LiveProgram.FirstTailBudget

end VPVNP
end Computability
end OAI
