import OAI.Optimization.LinearProgramming.Compression.MinorAssignments
import OAI.Optimization.LinearProgramming.Compression.ComputedEpoch
import OAI.Optimization.LinearProgramming.Compression.RequestNative

/-! An executed generator commitment and native lattice-reduced request procedure on the
nonzero minors of a rational complementary matrix pair. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

variable {r s n : ℕ} (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)

/-- The commitment to the current generators is computed from their sorted indices,
with all comparisons routed to the rational minor-magnitude oracle. -/
def matrixMinorCommit (fuel : ℕ) (J : Finset (NonzeroPairMinor D E)) : J → ℚ :=
  let e := (J.orderIsoOfFin rfl).toEquiv.symm
  let w := paperWidth n
  let H := epochHeightFor n J.card
  let mag (i : Fin J.card) := minorMagnitude D E (e.symm i).val
  computedEpochCommitWith e w H (Lattice.lllShortSelector (epochFormBudget J.card w H))
    (requestMagnitudeNegative fuel (paperRadius n + 7) mag)

theorem matrixMinorCommit_valid (fuel : ℕ) (J : Finset (NonzeroPairMinor D E)) :
    ValidEpochCommit (fun j : J => minorProxy D E fuel j.val) (paperWidth n)
      (epochHeightFor n J.card) (matrixMinorCommit D E fuel J) := by
  let e := (J.orderIsoOfFin rfl).toEquiv.symm
  let w := paperWidth n
  let H := epochHeightFor n J.card
  let mag (i : Fin J.card) := minorMagnitude D E (e.symm i).val
  apply computedEpochCommitWith_valid e (fun j : J => minorProxy D E fuel j.val) w H
    (Lattice.lllShortSelector (epochFormBudget J.card w H))
    (Lattice.lllShortSelector_correct (Nat.succ_pos _) (Nat.zero_lt_succ _))
    (requestMagnitudeNegative fuel (paperRadius n + 7) mag)
  exact requestMagnitudeNegative_correct _ _ mag (fun i => minorMagnitude_pos D E (e.symm i).val)

/-- Actual on-demand minor service. The outer loop stores one current generator set.
Only the listed generators and the requested minor enter either LLL computation. -/
def matrixMinorRequest (fuel : ℕ) : MinorRequest (NonzeroPairMinor D E) :=
  evaluateMinorRequest (matrixMinorCommit D E fuel)
    (nativeMinorRequest fuel (paperRadius n + 7) (paperGrid n) (minorMagnitude D E))

theorem matrixMinorRequest_restartTest (fuel : ℕ) :
    RestartTest (minorProxy D E fuel) (matrixMinorRequest D E fuel) :=
  nativeMinorRequest_restartTest fuel (paperRadius n + 7) (paperGrid n) (Nat.two_pow_pos _)
    (minorMagnitude D E) (minorMagnitude_pos D E) (matrixMinorCommit D E fuel)

/-- One assignment simultaneously extends every successful request at the same generators;
it has dimension-controlled bit lengths and all four-term clipping inequalities. -/
theorem matrixMinorRequest_common_all (fuel : ℕ) (hd : r+s=n)
    (J : Finset (NonzeroPairMinor D E)) (hJ : IsDissociated (minorProxy D E fuel) J) :
    ∃ f : NonzeroPairMinor D E → ℚ, ValidMinorAssignment n (minorTrueLog D E) f ∧
      ∀ u v, matrixMinorRequest D E fuel J u = some v → f u = v := by
  apply all_successful_requests_extend n (minorProxy D E fuel) (minorTrueLog D E)
    (minorProxy_close D E fuel) (fun I hI => (minorProxy_independent_bound_all D E fuel hd I hI).2)
    (nativeMinorRequest fuel (paperRadius n + 7) (paperGrid n) (minorMagnitude D E))
    (nativeMinorRequest_goodRequestRows n fuel (paperRadius n + 7) (minorMagnitude D E) (minorMagnitude_pos D E))
    (matrixMinorCommit D E fuel) (fun I _ => matrixMinorCommit_valid D E fuel I) J hJ

/-- Positive-dimension specialization used at a marked coordinate. -/
theorem matrixMinorRequest_common (fuel : ℕ) (_hn : 1 ≤ n) (hd : r+s=n)
    (J : Finset (NonzeroPairMinor D E)) (hJ : IsDissociated (minorProxy D E fuel) J) :
    ∃ f : NonzeroPairMinor D E → ℚ, ValidMinorAssignment n (minorTrueLog D E) f ∧
      ∀ u v, matrixMinorRequest D E fuel J u = some v → f u = v :=
  matrixMinorRequest_common_all D E fuel hd J hJ

end Compression
end LinearProgramming
end Optimization
end OAI
