import OAI.Computability.VPVNP.EvaluatorMonomialSchedule
import OAI.Computability.VPVNP.EvaluatorProgramRawInput

/-!
# The monomial scheduler on binary advice and exponents

Loading the self-delimiting fields, converting the native binary exponents
to radix digits, and traversing those digits are fixed controls. This links
their semantics to the chronological matrix-choice effect on the input
exponents. The callback specifications concern the two matrix steps.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorProgramMonomial

open RAMTape EvaluatorRoutine EvaluatorDigitFetch EvaluatorScheduleEffects
  EvaluatorMonomialSchedule EvaluatorRadixRows EvaluatorProgramRawInput

variable {P S I : Type} [DecidableEq P] [Fintype I] {t Z : ℕ}

/-- The radix converter followed by the monomial scheduler with the supplied Frobenius and
label-multiplication callbacks. -/
def nativeMachine (frobenius multiply : FiniteRoutine (Port P)) :=
  EvaluatorProgramInput.run (machine frobenius multiply)

/-- The complete monomial routine that loads the tagged raw input before executing the
converter and the two scheduled callbacks. -/
def rawMachine (ps : List P) (frobenius multiply : FiniteRoutine (Port P)) :=
  withReader ps (nativeMachine frobenius multiply)

variable (e : Fin t → BurstRAM.Word Z) (d : List Bool) (payload : S → Stacks P)
    (next : Option ℕ → S → I → S) (frobenius multiply : FiniteRoutine (Port P))
    (BF BM : ℕ)

local notation "data" => packedTable d.length (TapeWord.value d) (List.ofFn e)
local notation "post" => fun x => EvaluatorProgramInput.extend Z d
  (bank data t Z d.length 0 0 0 0 (payload x))
local notation "ticks" => EvaluatorProgramInput.convertTicks t Z d.length +
  budget t Z d.length (TapeWord.value d) BF BM

/-- The native little-endian exponent array reaches the chronological
Frobenius and label action sum. Its exact conversion time precedes the
scheduler's per-path budget. -/
theorem native_realizes (hq : 2 ≤ TapeWord.value d)
    (hf : ∀ (j : Fin Z) left, Realizes frobenius.body
      (fun x => bank data t Z d.length 0 j 0 left (payload x))
      (fun x => bank data t Z d.length 0 j 0 left (payload x)) BF (stepEffect next none))
    (hm : LabelCallback e d.length (TapeWord.value d) BM payload next multiply) :
    Realizes (nativeMachine frobenius multiply).body (EvaluatorProgramInput.initial e d ∘ payload)
      post ticks (schedulerEffect next e (TapeWord.value d)) :=
  EvaluatorProgramInput.run_realizes _ e d hq payload
    (machine_realizes e d.length (TapeWord.value d) BF BM payload next frobenius multiply
      (by omega) (TapeWord.value_lt d).le hf hm)

/-- The whole parser, radix converter, and scheduler start with just the
single advice-and-exponent stream on the input stack. -/
theorem raw_realizes (ps : List P) (hp : ps.Nodup) (hall : ∀ p, p ∈ ps)
    (R : ℕ) (hR : ∀ x, readTicks ps e d (payload x) ≤ R) (hq : 2 ≤ TapeWord.value d)
    (hf : ∀ (j : Fin Z) left, Realizes frobenius.body
      (fun x => bank data t Z d.length 0 j 0 left (payload x))
      (fun x => bank data t Z d.length 0 j 0 left (payload x)) BF (stepEffect next none))
    (hm : LabelCallback e d.length (TapeWord.value d) BM payload next multiply) :
    Realizes (rawMachine ps frobenius multiply).body
      (fun x => Evaluator.InputBank.frame (advice ps t d (payload x) ++ runtime e) (fun _ => []))
      (Evaluator.InputBank.frame [] ∘ (post)) (R + (ticks)) (schedulerEffect next e (TapeWord.value d)) :=
  withReader_realizes ps hp hall e d payload _ hR
    (native_realizes e d payload next frobenius multiply BF BM hq hf hm)

end EvaluatorProgramMonomial

end VPVNP
end Computability
end OAI
