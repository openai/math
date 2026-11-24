import OAI.Computability.VPVNP.LiveFirstTailBudget
import OAI.Computability.VPVNP.LiveLayoutWordFit

/-!
# Simultaneous size bounds for every group of the fixed evaluator

The address exponent is chosen after the evaluator and the label geometry.
For every larger fixed exponent, one eventual length threshold works for all
advice prefixes in the allocated region and for both endpoint routes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorRoutes

open BurstRAM PairStages CursorBounds CursorNetwork Filter LiveEvaluatorTailCost
open OutsideTailStages OutsideTailCount

/-- The evaluator tail fits the word geometry, the per-call probe allowance, and the total
budgets for its initial and ordinary groups. -/
structure TailFits (G : Group) (raw : ℕ) : Prop where
  fits : limit G < 2^G.w
  geometry : GeometryFit G (radius G)
  call : callBound G.w ≤ G.g.H
  ordinaryBudget : LiveHeaderSchedule.costBound (Header.sizes G.constants G.g)+4+2*routeCost G.w (radius G)+transitionCost (radius G) ≤ 2^G.g.d*G.g.H
  initialBudget : FirstTailBudget.cost G raw ≤ 2^G.g.d*G.g.H

private theorem ordinary_group_cost (u : Parameters) :
    2*routeCost u.wordWidth u.radius+transitionCost u.radius ≤ groupBound u false false false := by
  have hwords : LiveEvaluatorEncoding.fieldWords u.radius = u.configWords := by
    unfold LiveEvaluatorEncoding.fieldWords Parameters.configWords; omega
  have hroute : routeCost u.wordWidth u.radius = 4+(u.wordWidth+4)*u.configWords := by
    rw [routeCost,hwords,Nat.mul_comm]
  have htrans : transitionCost u.radius = u.transitionCost+u.configWords := by
    unfold transitionCost Parameters.transitionCost Parameters.configWords LiveEvaluatorRAM.Schedule.calls; omega
  rw [hroute,htrans,← groupBudget]
  simp only [firstBudget,lastBudget,Bool.false_eq_true,ite_false]
  omega

private theorem ordinary_cost_le (G : Group) (raw : ℕ) :
    LiveHeaderSchedule.costBound (Header.sizes G.constants G.g)+4+2*routeCost G.w (radius G)+transitionCost (radius G) ≤
      OutsideBudget.actualBound G.constants G.g raw false false false := by
  have h := ordinary_group_cost (params G raw)
  change 2*routeCost G.w (radius G)+transitionCost (radius G) ≤ groupBound (params G raw) false false false at h
  change _ ≤ LiveHeaderSchedule.costBound (Header.sizes G.constants G.g)+8+4*(G.constants.labels.eval G.g+1)+100+
    16*(OutsideBudget.auxWords (Header.sizes G.constants G.g) (G.constants.labels.eval G.g)+1)+
    7*(G.constants.labels.eval G.g*G.constants.Z.eval G.g+1)+groupBound (params G raw) false false false
  omega

set_option maxHeartbeats 800000 in
/-- The threshold in the input length is uniform in the route, advice and
model. The clock may be any common group clock above the live n^10000 cap. -/
theorem eventually_tailFits {C : ℕ} (u : PairExponents C) (c : Constants) (E : UniversalMachine.Program) :
    ∃ b₀, ∀ b ≥ b₀, ∀ᶠ n : ℕ in atTop, ∀ G : Group,
      G.g = paperGeometry b (liveCapacity u) n → G.constants = c → G.evaluator = E → n^10000 ≤ G.clock →
      ∀ raw, raw ≤ G.constants.prefixCapacity.eval G.g → TailFits G raw := by
  obtain ⟨b₀,bounds⟩ := OutsideTraces.eventually_all_caps u c E
  refine ⟨max 1 b₀, fun b hb => ?_⟩
  have hb₁ : 1 ≤ b := (le_max_left ..).trans hb
  have hshadow := ((Layout.shadow_sitePowers c).fits hb₁ (liveCapacity_polynomial u)).2
  let e := PublicExpr.lit (9*E.extra+2)
  have hs : e.SitePowers := trivial
  have hrows := (hs.fits hb₁ (liveCapacity_polynomial u)).2
  filter_upwards [bounds b ((le_max_right ..).trans hb),hshadow,hrows] with n bound shadow row
  intro G hg hc hE hclock raw hraw
  have fits : limit G < 2^G.w := by
    change (Layout.shadow G.constants).eval G.g < 2^G.g.w
    rw [hc,hg]; exact shadow.1
  have table : 9*G.evaluator.extra+2 < 2^G.w := by
    change 9*G.evaluator.extra+2 < 2^G.g.w
    rw [hE,hg]; exact row.1
  have hw : 2 ≤ G.w := by
    by_contra! h
    have small := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : G.w ≤ 1)
    have large := G.tagFit
    rw [pow_one] at small; omega
  obtain ⟨first, per, work⟩ := bound G hg hc hE raw true false false hraw
  have later := (bound G hg hc hE raw false false false hraw).1
  have clockFit : instructionBound G ≤ G.clock := (le_max_right ..).trans ((le_max_right ..).trans (work.trans hclock))
  have gather : 8*G.w+67 ≤ G.clock := (le_max_left ..).trans ((le_max_right ..).trans clockFit)
  have terminal : LiveEvaluatorRAM.Schedule.callFuel G.evaluator+47 ≤ G.clock :=
    (le_max_right ..).trans ((le_max_right ..).trans clockFit)
  have tick : LiveEvaluatorRAM.Schedule.callFuel G.evaluator ≤ G.clockAt Stage.transition := by
    have len : (LiveStageLink.dispatchEvents G.addr Stage.transition).length = 44 := rfl
    unfold Group.clockAt; rw [len]; omega
  have positive : 0 < G.g.H := (by decide : 0 < 26).trans_le ((le_max_left ..).trans per)
  have headroom : processorCount b n ≤ 2^G.g.d*G.g.H := by rw [hg] at positive ⊢; exact Nat.le_mul_of_pos_right _ positive
  exact ⟨fits,geometryFit G fits hw (by omega) (by omega) gather tick,(le_max_right ..).trans per,
    (ordinary_cost_le G raw).trans (later.le.trans headroom),
    (FirstTailBudget.cost_le_actualBound G raw).trans (first.le.trans headroom)⟩

end LiveProgram.EvaluatorRoutes

end VPVNP
end Computability
end OAI
