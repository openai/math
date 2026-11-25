import OAI.Optimization.LinearProgramming.PriceGame.CampaignRecovery
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionCharge
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionComplexity

/-! Unconditional correctness of the recursive expert algorithm of Sections 4–7. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Campaign

open Finset States.Mass Learning Charging

theorem guarantees {N R : ℕ} {anchor : Fin N} (hidden : Hidden N R anchor)
    (markets : AvailableMarkets N) : RoundGuarantees hidden markets := by
  constructor
  · intro p output reached
    obtain ⟨o, actual, rfl⟩ := (Computation.reaches_map_iff ..).mp reached
    exact TrialExecution.run_reaches_probeBudget hidden
      (populationExperts p) (markets (populationExperts p)) (populationWeights p) p.nonnegative o actual
  · intro p output reached sel roster compares miss
    obtain ⟨o, actual, rfl⟩ := (Computation.reaches_map_iff ..).mp reached
    have keeps : TrialExecution.LoggedComparisons hidden (populationExperts p) sel o.val.log := by
      intro pr hp s hs t ht
      exact compares s hs t (List.mem_flatMap.mpr ⟨pr,hp,ht⟩)
    have fails : ¬ (States.FiniteState.root hidden).wins hidden (fun _ _ => 0) o.val.prices := by
      intro success
      obtain ⟨i,hi,less⟩ := of_decide_eq_true miss
      have ok := success i hi
      have bound : (R+1:ℚ) - (hidden.cost i : ℕ) ≤ hidden.signedPrice (o.val.prices i) := by
        simpa [States.FiniteState.value,States.FiniteState.shift,States.FiniteState.decode,
          States.FiniteState.root,rootVertex,States.priority,States.signed,Hidden.signedPrice] using! ok
      exact (not_lt_of_ge bound) less
    have charge := TrialExecution.run_failure_charge hidden (populationExperts p)
      (markets (populationExperts p)) sel roster (populationWeights p) p.nonnegative o actual keeps fails
    unfold weighted at charge
    rw [rootWeight_eq_skeleton_charge] at charge
    simpa [resultOf,readScore,rootSkeleton] using! charge

/-- The paper's source-level recursive algorithm succeeds on every admissible designated-label
transcript. Its query count is stated separately from a simulation on a bit machine. -/
theorem recover_sign {N R : ℕ} {anchor : Fin N} (hidden : Hidden N R anchor)
    (hR : 0 < R) : Tree.Correct hidden (referenceStrategy R (rounds N R) anchor) :=
  correct_of_roundGuarantees hidden hR _ (guarantees hidden _)

private theorem combine_query_bounds {answer T q x upper : ℕ} (p b k d : ℕ)
    (work : answer ≤ T * q) (trialCount : T = x^p)
    (queries : q ≤ upper^k) (upperBound : upper ≤ x^b) (deg : p+b*k = d) :
    answer ≤ x^d := by
  calc
    _ ≤ T*q := work
    _ ≤ x^p * (x^b)^k := Nat.mul_le_mul trialCount.le
      (queries.trans (Nat.pow_le_pow_left upperBound k))
    _ = _ := by rw [← pow_mul, ← pow_add, deg]

set_option exponentiation.threshold 300 in
/-- With the fixed effective trial count, at most a fixed polynomial number of queries
are asked even when every reply is inconsistent. -/
theorem recursive_query_bound {N : ℕ} (R : ℕ) (anchor : Fin N) :
    (referenceStrategy R (rounds N R) anchor).height ≤ (inputSize N R)^1510 := by
  have X2 : 2 ≤ inputSize N R := by
    have := anchor.isLt
    simp only [inputSize]
    omega
  have Xn : N+1 ≤ inputSize N R := by simp [inputSize, Nat.add_assoc]
  have hbase : 2*(N+1) ≤ (inputSize N R)^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul X2 Xn
  exact combine_query_bounds (x := inputSize N R) (T := rounds N R) 300 2 605 1510
    (strategy_height R (rounds N R) anchor (fun xs => TrialExecution.marketSolverAtCommonWeightUnit xs))
    (rounds_eq N R) (TrialExecution.queryBound_polynomial N) hbase rfl

/-- The ceil logarithm in the manuscript and the floor logarithm in the comparator
differ by at most one input bit. -/
theorem inputSize_le_machine (N R : ℕ) :
    inputSize N R ≤ 2 * (N + (R+1).log2 + 1) := by
  have hp : R+1 < 2 ^ ((R+1).log2+1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by decide) _
  have hs : R.size ≤ (R+1).log2+1 := Nat.size_le.mpr ((Nat.lt_succ_self R).trans hp)
  unfold inputSize
  omega

private theorem substitute_size {cost size scale raw : ℕ} (d : ℕ)
    (first : cost ≤ size^d) (second : size ≤ scale*raw) : cost ≤ scale^d * raw^d :=
  (first.trans (Nat.pow_le_pow_left second d)).trans_eq (Nat.mul_pow scale raw d)

theorem recursive_query_bound_machine {N : ℕ} (R : ℕ) (anchor : Fin N) :
    (referenceStrategy R (rounds N R) anchor).height ≤
      2^1510 * (N+(R+1).log2+1)^1510 := by
  exact substitute_size 1510 (recursive_query_bound R anchor) (inputSize_le_machine N R)

end Campaign
end PriceGame
end LinearProgramming
end Optimization
end OAI
