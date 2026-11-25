import OAI.Optimization.LinearProgramming.PrimalDual.CallSegmentsCore
import OAI.Optimization.LinearProgramming.PrimalDual.Ending
import OAI.Optimization.LinearProgramming.PrimalDual.FrameOptimizationCompose

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace CallSegments

open RAM RAM.Call RAM.Tape RAM.Block Polynomial Bridge

/-- The program used as the witness in the strongly polynomial optimization reduction. -/
def program (p : Program) (C E : ℕ) : Program :=
  withFirstCall p C E firstReturn (endingCode p)

inductive Answer where
  | certificate | optimum | ray

def Answer.guestTag : Answer → ℕ | .certificate => 1 | _ => 0
def Answer.tag : Answer → ℕ | .certificate => 0 | .optimum => 1 | .ray => 2
def Answer.calls : Answer → ℕ | .certificate => 1 | _ => 2

def firstParts (p : Program) (C E : ℕ) {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (tag : ℕ) : List Part :=
  let off := firstReturnBase p C E
  [.fixed 0 (firstPrelude p C E), .embedded (firstPrelude p C E).size (firstReturn off)
    [m,d] (lpInput A b) (FeasibilityOutput A b) tag]

def jointParts (p : Program) (C E : ℕ) {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) (c : Fin d → ℚ) (tag : ℕ) : List Part :=
  let off := firstReturnBase p C E
  let matrix := finJointMatrix A b c
  let rhs := finJointRhs b c
  [.fixed (endingBlocks.stagePC off) stageJoint, .fixed (endingBlocks.prepPC off) prepareCallInputs,
   .embedded (endingBlocks.callPC off) (endingBlocks.secondRet off) [rowCount m d,d+m]
     (lpInput matrix rhs) (FeasibilityOutput matrix rhs) tag]

def itinerary (p : Program) (C E : ℕ) {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) (c : Fin d → ℚ) (answer : Answer) : List Part :=
  let off := firstReturnBase p C E
  firstParts p C E A b answer.guestTag ++ match answer with
  | .certificate => [.terminal off firstCertificate 0]
  | .optimum => jointParts p C E A b c 0 ++ [.terminal (endingBlocks.optPC off) secondOptimum 1]
  | .ray => jointParts p C E A b c 1 ++ [.terminal (endingBlocks.rayPC off) secondRay 2]

theorem count_itinerary (p : Program) (C E : ℕ) {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) (c : Fin d → ℚ) (answer : Answer) :
    count (itinerary p C E A b c answer) = answer.calls := by cases answer <;> rfl

theorem Answer.calls_le_two (answer : Answer) : answer.calls ≤ 2 := by cases answer <;> decide

noncomputable def time (p : Program) (C E : ℕ) : Polynomial ℕ :=
  firstTimePolynomial p C E + endingPolynomial (firstWindowPolynomial p C E) (oraclePolynomial C E)

/-- This is the per-program numerical guarantee inside `StronglyPolynomialFeasibility`. -/
def BoundedSolver (p : Program) (C E bC bE : ℕ) : Prop :=
  ∀ (m d : ℕ), 0 < m → 0 < d → ∀ (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ),
    ∃ (k : ℕ) (tr : Fin (k+1) → State ℚ), Trace p (start [m,d] (lpInput A b)) k tr ∧
      k ≤ polyBound C E (m+d) ∧ (∀ i, scalarBound (polyBound bC bE (totalBits (lpInput A b))) (tr i)) ∧
      FeasibilityOutput A b (tr (Fin.last k))

end CallSegments
end PrimalDual
end LinearProgramming
end Optimization
end OAI
