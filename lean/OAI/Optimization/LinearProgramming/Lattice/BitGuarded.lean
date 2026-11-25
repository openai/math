import OAI.Optimization.LinearProgramming.OracleSpec.PolynomialFuel

/-! Fixed bit-stack loops with a checked word-length bound. A malformed initial array may
contain arbitrary integers. Each actual step is computed from its input and its result is
retained exactly when it fits the unary budget. On valid LLL traces the cap is never reached. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec.Fuel

variable {S I : Type}

def boundedStateCode (es : S → List Bool) := prodCode unaryCode es

def cappedTransition (es : S → List Bool) (f : S → S) (x : ℕ × S) : ℕ × S :=
  if (es (f x.2)).length ≤ x.1 then (x.1, f x.2) else x

/-- A real bit-stack guard using the length of the computed candidate. -/
noncomputable def cappedTransitionP {es : S → List Bool} {f : S → S} (next : Procedure es es f) :
    Procedure (boundedStateCode es) (boundedStateCode es) (cappedTransition es f) := by
  let cap := first unaryCode es
  let state := second unaryCode es
  let candidate := next.comp state
  let guard := unaryLe.comp (((lengthInUnary es).comp candidate).pair cap)
  let original := identity (boundedStateCode es)
  refine (((choose original (cap.pair candidate)).comp (guard.pair original)).congrFun ?_)
  intro x
  change (if decide ((es (f x.2)).length ≤ x.1) then (x.1, f x.2) else x) = _
  by_cases h : (es (f x.2)).length ≤ x.1 <;> simp [cappedTransition, h]

private theorem cappedTransition_iterate_size (es : S → List Bool) (f : S → S) (x : ℕ × S) (i : ℕ) :
    (((cappedTransition es f)^[i]) x).1 = x.1 ∧
    (es (((cappedTransition es f)^[i]) x).2).length ≤ max x.1 (es x.2).length := by
  induction i with
  | zero => exact ⟨rfl, le_max_right ..⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    unfold cappedTransition
    split
    · rename_i h
      exact ⟨ih.1, (h.trans_eq ih.1).trans (le_max_left ..)⟩
    · exact ih

/-- All iterations on arbitrary encoded states have a linear word-length bound. -/
theorem cappedTransition_growth (es : S → List Bool) (f : S → S) (n : ℕ) (x : ℕ × S) (i : ℕ) :
    (boundedStateCode es (((cappedTransition es f)^[i]) x)).length ≤
      (Polynomial.C 2 * Polynomial.X : Polynomial ℕ).eval (n + (boundedStateCode es x).length) := by
  have h := cappedTransition_iterate_size es f x i
  simp only [boundedStateCode, prodCode, pairBits_length, unaryCode, List.length_replicate,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, h.1]
  omega

/-- Compute both budgets from the actual input word, initialize the work state, and execute
the fixed transition the requested number of times. -/
noncomputable def cappedIterationP {ei : I → List Bool} {es : S → List Bool} {init : I → S}
    {step : S → S} (start : Procedure ei es init) (next : Procedure es es step)
    (time space : Polynomial ℕ) :
    Procedure ei es (fun a => (((cappedTransition es step)^[time.eval (ei a).length])
      (space.eval (ei a).length, init a)).2) :=
  (second unaryCode es).comp ((cappedTransitionP next).iterate (Polynomial.C 2 * Polynomial.X)
    (fun n x i _ => cappedTransition_growth es step n x i) |>.comp
      ((clock ei time).pair ((clock ei space).pair start)))

/-- Agreement with ordinary transitions on all executions satisfying the width estimate. -/
theorem cappedTransition_iterate_exact (es : S → List Bool) (step : S → S) (s : S) (cap t : ℕ)
    (hfit : ∀ j, 0 < j → j ≤ t → (es ((step^[j]) s)).length ≤ cap) :
    ((cappedTransition es step)^[t]) (cap,s) = (cap,(step^[t]) s) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp := ih fun j hj h => hfit j hj (Nat.le_succ_of_le h)
    rw [Function.iterate_succ_apply', hp]
    have ht := hfit (t+1) (Nat.succ_pos _) le_rfl
    rw [Function.iterate_succ_apply'] at ht
    simp [cappedTransition, ht, Function.iterate_succ_apply']

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
