import OAI.Computability.NearSquareRoot.PrecisionNodeChild
import OAI.Computability.NearSquareRoot.PrecisionPlanMix
import OAI.Computability.NearSquareRoot.PrecisionPlanScale
import OAI.Computability.NearSquareRoot.PrecisionPlanXor

/-! # One recursive template with all of its actual guarded leaves -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace PhysicalWalshNode

open KernelPass PhysicalWalsh PhysicalWalshGrid

/-- Unitary child and permutation leaves propagate earlier input error with
gain one. The nonunitary rational leaves use their explicit dyadic row sums. -/
def coefficientFactor {a : ℕ} : LeafFactor (a+1)
  | _, _, .mix c => mixGain c
  | _, _, .scale _ _ c => KernelScaleNorm.gain c
  | _, _, _ => 0

def templateFactor {a i o : ℕ} (p : Plan (a+1) i o) : ℕ := numericalFactor coefficientFactor p

theorem nodePlan_numericalStep {a W : ℕ} (hW : 0 < W) (plan : Plan (a+1) W W)
    (s : Shape) (hs : 0 < s.level) (frac : ℕ) {T R δ : ℝ}
    (hT : 0 ≤ T) (hR : 1 ≤ R) (hδ : 0 ≤ δ) (room : T*2^frac < 2^s.w)
    (fault : Real.sqrt (laneCount a W s) * ((2:ℝ)/2^frac) ≤ δ)
    (children : ∀ axis, NodeAccurate hW plan frac (descend (a+1) W axis s) R T δ) :
    NumericalStep (nodeOps hW plan) (idealOps a W (childIdeal a W)) (nodeGuards hW plan) s
      (laneSize a W s) (laneGap a W frac s) plan (templateFactor plan) (T/R-1) δ := by
  have hroom : (T/R-1)*2^frac < 2^s.w :=
    (mul_le_mul_of_nonneg_right (nextCap_le hT hR) (by positivity)).trans_lt room
  apply planNumericalStep _ _ _ _ _ _ coefficientFactor hδ
  intro i o t ht
  cases t with
  | mix c =>
    simpa only [numericalFactor,coefficientFactor,Nat.cast_add,Nat.cast_one] using
      mix_numericalStep hW plan s hs frac (childIdeal a W) c hδ hroom fault
  | xor g =>
    simpa only [numericalFactor,coefficientFactor,Nat.zero_add,Nat.cast_one] using
      xor_numericalStep hW plan (childIdeal a W) s hs frac (T/R-1) δ hδ g
  | scale q test table =>
    simpa only [numericalFactor,coefficientFactor,Nat.cast_add,Nat.cast_one] using
      scale_numericalStep hW plan (childIdeal a W) s hs frac (T/R-1) δ hδ hroom fault test table
  | child g =>
    simpa only [numericalFactor,coefficientFactor,Nat.zero_add,Nat.cast_one] using
      child_numericalStep hW plan s hs frac g (lt_of_lt_of_le zero_lt_one hR) hδ (children g)
  | seq _ _ | parallel _ _ => cases ht

end PhysicalWalshNode

end

end NearSquareRoot
end Computability
end OAI
