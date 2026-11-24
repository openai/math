import OAI.Computability.VPVNP.FixedProgramTailInitialization
import OAI.Computability.VPVNP.LiveTailContinuation

/-!
# The fixed diagonal program realizes its model's evaluator half

This identifies the physical table's continuation with the certificate's
initial-code function, using the actual model advice, row permutation and
integer counter widths. The program geometry fixes the remaining dimensions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM Compression LiveProgram LiveEvaluatorEncoding LabelEvaluator JointLabelSystem
open EvaluatorRoutes LocalCount
open OutsideTailStages OutsideTailCount
open scoped Fin.CommRing

private theorem transportTail {G : PairStages.Group} {S H t t' z z' M M' Δ a : ℕ}
    (W : Conditions G S H) (hd : Δ = (profile G).delta) (ha : a = (profile G).advice)
    (ht : t = t') (hz : z = z') (hM : M = M')
    (actualAdvice : CutSchedule.Bits (profile G).advice) (modelAdvice : CutSchedule.Bits a)
    (advice : HEq actualAdvice modelAdvice)
    (actualFit : 1+t*z ≤ (profile G).delta) (modelFit : 1+t'*z' ≤ Δ)
    (actualLayout : LiveEvaluatorTail.Layout G.evaluator.extra M G.w (profile G).delta)
    (modelLayout : LiveEvaluatorTail.Layout G.evaluator.extra M' G.w Δ)
    (actualInit : (Fin t → ℕ) → Code G.evaluator.extra M) (modelInit : (Fin t' → ℕ) → Code G.evaluator.extra M')
    (initial : HEq actualInit modelInit) (result : TailContinuation W actualAdvice actualFit actualLayout actualInit) :
    tailObligation W hd ha modelAdvice modelFit modelLayout modelInit := by
  subst Δ; subst a; subst t'; subst z'; subst M'
  rw [eq_of_heq advice, eq_of_heq initial] at result
  exact result

variable {K : Type*} [Field K] {S : BlockSchedule K} {D : Program} {B : S.Templates} {n C : ℕ}
variable {hn : 2 ≤ n} {p : Nat.Primes} {M : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
variable (data : D.ScalarData B hn M) {ht : 21 ≤ 2^(D.geometry n).w} {hf : 44 ≤ n^10000}
local notation "G" => D.executionGroup n ht hf

set_option maxHeartbeats 800000 in
/-- Native realization used by `assembleLocalCertificate`. The model
provides the raw input, its exact ordering, and the occupied initial tape
interval. Only the numerical caps on the common table enter separately. -/
theorem fixedTailObligation
    (W : Conditions G (2^(D.geometry n).d) (D.geometry n).H)
    (hC : D.constants.circuitExponent = C) (hm : D.constants.motifLabels = Fintype.card B.Entry)
    (fit : 1+B.denseCount n C*D.counterWidth n ≤ n^D.constants.deltaPower)
    (layout : LiveEvaluatorTail.Layout D.evaluator.extra (n^D.constants.radiusPower) (D.geometry n).w (n^D.constants.deltaPower))
    (fits : limit G < 2^(D.geometry n).w) (geom : GeometryFit G (radius G)) (call : callBound (D.geometry n).w ≤ (D.geometry n).H)
    (ordinaryBudget : LiveHeaderSchedule.costBound (sizes G)+4+2*routeCost (D.geometry n).w (radius G)+transitionCost (radius G) ≤
      2^(D.geometry n).d*(D.geometry n).H)
    (initialBudget : LiveHeaderSchedule.costBound (sizes G)+4+8+packWork (params G data.raw.length)+inputWork (params G data.raw.length)+
      routeCost (D.geometry n).w (radius G)+transitionCost (radius G) ≤ 2^(D.geometry n).d*(D.geometry n).H) :
    tailObligation W deltas adviceSizes data.advice fit layout data.init := by
  have count : FirstTailHeader.labelCount G = B.denseCount n C := physicalLabelCount_eq D B hC hm
  have formalCount := count.trans (FixedRows.labelOrder_length B.Entry n C)
  have width : FirstTailHeader.exponentWidth G = D.counterWidth n := physicalCounterWidth_eq D
  have rad : radius G = n^D.constants.radiusPower := physicalRadius_eq D
  have delta : n^D.constants.deltaPower = (sizes G).delta := deltas
  have adviceSize : n^D.constants.advicePower = (sizes G).advice := adviceSizes
  have prefixCap : D.constants.prefixCapacity.eval (D.geometry n) = n^D.constants.prefixPower := by
    rw [Constants.prefixCapacity, PublicExpr.eval_natPow]; rfl
  let order := nativeLabelOrder D B count
  let values := nativeOrdinalWords D B count
  have cut : 1+FirstTailHeader.labelCount G*FirstTailHeader.exponentWidth G ≤ (sizes G).delta := by rwa [count,width,← delta]
  have image : LiveEvaluatorTail.Layout D.evaluator.extra (radius G) (D.geometry n).w (sizes G).delta := by rwa [rad,← delta]
  have cap : (D.geometry n).w+D.constants.prefixCapacity.eval (D.geometry n)+FirstTailHeader.labelCount G*Nat.clog 2 (FirstTailHeader.labelCount G)
      ≤ (sizes G).advice := by
    rw [prefixCap, ← adviceSize, show Nat.clog 2 (FirstTailHeader.labelCount G) = Nat.clog 2 (B.compressorLabelCount C n) from
      congrArg (Nat.clog 2) formalCount, count]; exact data.adviceSpace
  have room : D.evaluator.extra ≠ 0 → data.raw.length+(2*(FirstTailHeader.labelCount G*FirstTailHeader.exponentWidth G)+
      6*FirstTailHeader.exponentWidth G+4) ≤ radius G+1 := by
    rw [formalCount,width,rad]; exact data.initialRoom D B
  let adv := Advice.adviceTape (D.geometry n).w (D.constants.prefixCapacity.eval (D.geometry n)) (sizes G).advice data.raw values
  have tape : HEq adv data.advice := by
    dsimp only [adv]
    rw [prefixCap,← adviceSize]
    exact heq_of_eq (nativeAdvice_eq D B count data.raw)
  have actual := tailContinuation G W fits geom cut image data.raw order values (fun _ => rfl) cap
    (prefixCap ▸ data.rawLength) room call ordinaryBudget initialBudget
  exact transportTail W delta adviceSize count width rad adv data.advice tape cut fit image layout _ data.init
    (midpointInitial_heq D B count data (ht := ht) (hf := hf)) actual

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
