import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionAssemble
import OAI.Optimization.LinearProgramming.PriceGame.ChargingTrial
import Mathlib.Logic.Equiv.Fin.Basic

/-! The means read from the two groups of an executed schedule are the means
used when charging that same schedule's rounded expert scores. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open Finset Charging Moment

/-- Flatten the probe group followed by the final group, in execution order. -/
def groupedIndex (r : ℕ) : Fin r ⊕ Fin r ≃ Fin (2*r) :=
  finSumFinEquiv.trans (finCongr (by omega))

@[simp] theorem groupedIndex_probe {r : ℕ} (j : Fin r) :
    groupedIndex r (.inl j) = probeIndex j := rfl

@[simp] theorem groupedIndex_final {r : ℕ} (j : Fin r) :
    groupedIndex r (.inr j) = finalIndex j := rfl

theorem weighted_uniform_eq (k : ℕ) (f : Calls k → ℚ) :
    weighted (uniform k) f = (∑ i, f i) / ((2*k+1 : ℕ) : ℚ) := by
  simp only [weighted, uniform, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
    ← Finset.mul_sum]
  ring

theorem weighted_groups_eq (k : ℕ) (f : Fin (2*(2*k+1)) → ℚ) :
    weighted (childWeights (uniform k)) (fun j => f (groupedIndex _ j)) =
      (∑ i, f i) / ((2*(2*k+1) : ℕ) : ℚ) := by
  have hu (j : Calls k ⊕ Calls k) : childWeights (uniform k) j =
      1 / ((2*(2*k+1) : ℕ) : ℚ) := by
    cases j <;> simp [childWeights, uniform] <;> ring
  have hs : (∑ i : Calls k ⊕ Calls k, f (groupedIndex (2*k+1) i)) = ∑ j, f j :=
    (groupedIndex (2*k+1)).sum_comp f
  simp only [weighted, hu, ← Finset.mul_sum, hs]
  ring

set_option exponentiation.threshold 512 in
theorem paper_sigma_eq : ((1/16 : ℚ) / (32*(8/(1/16 : ℚ)^65))) = sigmaQ := by
  norm_num [sigmaQ]

theorem rationalScore_eq_roundCharge (q : ℚ) : rationalScore scaleQ sigmaQ q = roundCharge sigmaQ q :=
  rfl

variable {N ne l k : ℕ}

/-- The stored score for a local expert rounds the signed gain from the probe half only. -/
theorem nodeScores_local (experts : Fin ne → Expert N)
    (xs : Fin (2*(2*k+1)) → Call N ne (2*k+1) l) (e : Fin ne) (localExpert : mask experts l e = true) :
    (nodeScores experts xs)[e] = roundCharge sigmaQ
      (weighted (uniform k) (fun j => callGain (xs (probeIndex j)) e)) := by
  rw [nodeScores_eq, weighted_uniform_eq]
  simp [nodeTrace, Trial.score, localExpert, rationalScore_eq_roundCharge, meanQ,
    ← Fin.sum_univ_eq_sum_range, scheduleGain]

/-- The score for a deeper expert rounds the mean of the actual cached child scores
in both groups. The group coordinate is translated by the actual execution schedule. -/
theorem nodeScores_deeper (experts : Fin ne → Expert N)
    (xs : Fin (2*(2*k+1)) → Call N ne (2*k+1) l) (e : Fin ne) (deepExpert : mask experts l e = false) :
    (nodeScores experts xs)[e] = roundCharge sigmaQ
      (weighted (childWeights (uniform k)) (fun j => (callScore (xs (groupedIndex _ j)) e : ℚ))) := by
  rw [nodeScores_eq, weighted_groups_eq k (fun i => (callScore (xs i) e : ℚ))]
  have hi (j : Fin (2*(2*k+1))) : (callScore (xs j) e : ℚ) =
      ((xs j).child.trace.score scaleQ sigmaQ e : ℚ) :=
    congrArg (fun n : ℕ => (n : ℚ)) ((xs j).child.scores_eq e)
  simp_rw [hi]
  simp [nodeTrace, Trial.score, deepExpert, rationalScore_eq_roundCharge, meanQ,
    ← Fin.sum_univ_eq_sum_range, scheduleChildren]

/-- At an actual assembled node the trace and the cached expert score agree with the
two charging expressions, even when the same expert identifier occurs on many tuples. -/
theorem assembled_score_eq_charge (experts : Fin ne → Expert N) (history : History N) (w : Weights ne)
    (run : NodeRun experts w (2*k+1) l) (e : Fin ne) :
    (assemble experts history w run).val.trace.score scaleQ sigmaQ e =
      if mask experts l e then roundCharge sigmaQ
        (weighted (uniform k) (fun j => callGain (run.val (probeIndex j)) e))
      else roundCharge sigmaQ
        (weighted (childWeights (uniform k)) (fun j => (callScore (run.val (groupedIndex _ j)) e : ℚ))) := by
  rw [← (assemble experts history w run).val.scores_eq e]
  cases hm : mask experts l e
  · exact nodeScores_deeper experts run.val e hm
  · exact nodeScores_local experts run.val e hm

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
