import OAI.Computability.VPVNP.EvaluatorChronologicalLoop
import OAI.Computability.VPVNP.EvaluatorDigitAction
import OAI.Computability.VPVNP.EvaluatorScheduleEffects

/-! # A fixed stack control for the monomial query schedule

The only two callbacks in this control are matrix-entry steps. Every other
instruction, from addressing the compact binary digit to advancing the row or
column, is the same at every exponent width. The continuation effect equals
the ordered sequence of index choices in the paper's digit program.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorMonomialSchedule

open RAMTape EvaluatorDigitFetch EvaluatorRoutine EvaluatorChronologicalLoop
  EvaluatorDigitAction EvaluatorScheduleEffects EvaluatorRadixRows

variable {P S I : Type} [DecidableEq P] [Fintype I]

/-- Finite scheduler code parametrized solely by its two matrix-step subroutines. -/
def machine (frobenius multiply : FiniteRoutine (Port P)) : FiniteRoutine (Port P) :=
  traverse frobenius (cellRoutine multiply)

/-- This instruction budget permits both matrix steps to use variable time
on different index paths. -/
def budget (t Z ℓ Q BF BM : ℕ) := traverseBudget t Z BF (cellBudget t Z ℓ Q BM)

variable {t Z : ℕ} (e : Fin t → BurstRAM.Word Z) (ℓ Q BF BM : ℕ) (payload : S → Stacks P)
    (next : Option ℕ → S → I → S) (frobenius multiply : FiniteRoutine (Port P))

local notation "data" => packedTable ℓ Q (List.ofFn e)

/-- The label step preserves its current binary counter while updating the
payload by the matrix-index choice. -/
def LabelCallback : Prop :=
  ∀ (i : Fin t) (j : Fin Z) labelsLeft colsLeft (x : S) (bits : List Bool) fuel,
    bits.length = ℓ → BM ≤ fuel → ∃ delay : I → ℕ, (∀ a, delay a ≤ BM) ∧ ∀ c,
      let input (s : S) := EvaluatorDigitRepeat.frame Port.digit Port.borrow
        (bank data t Z ℓ i.val j.val labelsLeft colsLeft (payload s)) bits []
      multiply.body.count c fuel (input x) = ∑ a, c (fuel-delay a) (input (next (some i.val) x a))

/-- With the two matrix-step semantics, the stack program realizes the
chronological action sum at every clock covering its explicit bound. -/
theorem machine_realizes (hq : 0 < Q) (hfit : Q ≤ 2^ℓ)
    (hf : ∀ (j : Fin Z) colsLeft, Realizes frobenius.body
      (fun x => bank data t Z ℓ 0 j 0 colsLeft (payload x))
      (fun x => bank data t Z ℓ 0 j 0 colsLeft (payload x)) BF (stepEffect next none))
    (hm : LabelCallback e ℓ Q BM payload next multiply) :
    Realizes (machine frobenius multiply).body
      (fun x => bank data t Z ℓ 0 0 0 Z (payload x))
      (fun x => bank data t Z ℓ 0 0 0 0 (payload x))
      (budget t Z ℓ Q BF BM) (schedulerEffect next e Q) := by
  apply traverse_realizes data t Z ℓ payload frobenius (cellRoutine multiply) BF
    (cellBudget t Z ℓ Q BM) (stepEffect next none) (cellEffect next e Q)
  · intro j left hj
    exact hf ⟨j, by omega⟩ left
  · intro j cols hj i labels hi
    let j' : Fin Z := ⟨j, by omega⟩
    let i' : Fin t := ⟨i, by omega⟩
    have h := cellRoutine_realizes multiply payload (next (some i)) e ℓ Q BM hq hfit
      i' j' labels cols (hm i' j' labels cols)
    change Realizes _ _ _ _ (repeatEffect next (some i) (digitAt Q e i'.val j'.val))
    rw [digitAt_fin]
    exact h

end EvaluatorMonomialSchedule

end VPVNP
end Computability
end OAI
