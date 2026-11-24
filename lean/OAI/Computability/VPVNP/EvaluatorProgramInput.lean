import OAI.Computability.VPVNP.EvaluatorDigitFetch
import OAI.Computability.VPVNP.EvaluatorRadixRows
import OAI.Computability.VPVNP.EvaluatorRoutine
import OAI.Computability.VPVNP.EvaluatorRoutineFrame

/-!
# Native input conversion and the finite-algebra evaluator

The row converter receives the binary exponent array in its native ascending,
little-endian order. Its digit output is the scheduler's table stack. This
allows traversal to start directly at column zero while preserving the
divisor, the unary width, and the callback's state.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorProgramInput

open RAMTape EvaluatorRoutine

/-- The packed binary input and its size counters, the division registers and the digit
scheduler's ports. -/
inductive Port (P : Type) where
  | input | width | rowCount | rounds
  | word (k : TapeWord.DivisionStack.Port)
  | sched (k : EvaluatorDigitFetch.Port P)
  deriving DecidableEq, Fintype

variable {P : Type}

/-- The radix converter writes its output directly onto the scheduler table. -/
def radixPort : EvaluatorRadixRows.Port → Port P
  | .input => .input
  | .width => .width
  | .rowCount => .rowCount
  | .radix .rounds => .rounds
  | .radix (.word k) => .word k
  | .radix .digits => .sched .table

private theorem radixPort_injective : Function.Injective (radixPort (P := P)) := by
  let back : Port P → EvaluatorRadixRows.Port
    | .input => .input
    | .width => .width
    | .rowCount => .rowCount
    | .rounds => .radix .rounds
    | .word k => .radix (.word k)
    | .sched _ => .radix .digits
  apply Function.LeftInverse.injective (f := radixPort) (g := back)
  intro k
  cases k with
  | radix k => cases k <;> rfl
  | _ => rfl

/-- Framing a scheduler bank retains the original divisor and row width.
All private conversion scratch is empty. -/
def extend (Z : ℕ) (d : List Bool) (s : Stacks (EvaluatorDigitFetch.Port P)) : Stacks (Port P)
  | .width => List.replicate Z true
  | .word .divisor => d
  | .sched k => s k
  | _ => []

variable {t Z : ℕ}

/-- Place the binary exponent vector and dimensions on the input stacks. The
callback payload can contain its advice and its initial arithmetic registers. -/
def initial (e : Fin t → BurstRAM.Word Z) (d : List Bool) (payload : Stacks P) : Stacks (Port P)
  | .rowCount => List.replicate t true
  | .word .original => List.ofFn (RAMSerialization.arrayBits t Z e)
  | k => extend Z d (EvaluatorDigitFetch.bank [] t Z d.length 0 0 0 Z payload) k

/-- The conversion code is independent of both runtime dimensions and the divisor. -/
def convert : FiniteRoutine (Port P) := EvaluatorRadixRows.nativeRows.onPorts radixPort

/-- Instruction count for moving the binary exponent array to the converter and running its
radix-row routine. -/
def convertTicks (t Z ℓ : ℕ) := 2*(t*Z) + 1 + EvaluatorRadixRows.rowsTicks t Z ℓ

/-- The packed table and the initial loop counters reach the scheduler together. -/
theorem convert_runs [DecidableEq P] (e : Fin t → BurstRAM.Word Z) (d : List Bool)
    (payload : Stacks P) (hq : 2 ≤ TapeWord.value d) :
    convert.Runs (convertTicks t Z d.length) (initial e d payload)
      (extend Z d (EvaluatorDigitFetch.bank
        (EvaluatorRadixRows.packedTable d.length (TapeWord.value d) (List.ofFn e))
        t Z d.length 0 0 0 Z payload)) := by
  apply EvaluatorRadixRows.nativeRows.runs_onPorts_framed radixPort_injective
    (EvaluatorRadixRows.native_array_runs e [] d [] hq)
  · intro k
    cases k with
    | radix k => cases k with
      | word k => cases k <;> rfl
      | rounds | digits => rfl
    | _ => rfl
  · intro k
    cases k with
    | radix k => cases k with
      | word k => cases k <;> rfl
      | rounds => rfl
      | digits => simp only [List.append_nil]; rfl
    | _ => rfl
  · intro k hk
    cases k with
    | sched k => cases k with
      | table => exact (hk (.radix .digits) rfl).elim
      | _ => rfl
    | word k => exact (hk (.radix (.word k)) rfl).elim
    | rowCount => exact (hk .rowCount rfl).elim
    | _ => rfl

/-- Run a scheduler from the native exponent input. The state space of the
linked routine depends only on the fixed converter and scheduler programs. -/
def run (scheduler : FiniteRoutine (EvaluatorDigitFetch.Port P)) : FiniteRoutine (Port P) :=
  convert.followedBy (scheduler.onPorts .sched)

private theorem realizes_sched [DecidableEq P] {S T : Type*}
    (scheduler : FiniteRoutine (EvaluatorDigitFetch.Port P))
    (Z : ℕ) (d : List Bool) {pre : S → Stacks (EvaluatorDigitFetch.Port P)}
    {post : T → Stacks (EvaluatorDigitFetch.Port P)} {B : ℕ}
    {effect : (T → ℕ) → S → ℕ} (h : Realizes scheduler.body pre post B effect) :
    Realizes (scheduler.onPorts Port.sched).body (extend Z d ∘ pre) (extend Z d ∘ post) B effect := by
  intro extra fuel hf x f c hc
  have hp : Function.Injective (Port.sched (P := P)) := fun _ _ h => Port.sched.inj h
  rw [scheduler.count_onPorts _ hp]
  apply h extra fuel hf x f
  intro y n hn
  have he : installStacks Port.sched ((extend Z d ∘ pre) x) (post y) = (extend Z d ∘ post) y := by
    apply installStacks_frame (small := post y) (target := (extend Z d ∘ post) y) hp (fun _ => rfl)
    intro k hk
    cases k with
    | sched k => exact (hk k rfl).elim
    | word k => cases k <;> rfl
    | _ => rfl
  rw [he]
  exact hc y n hn

/-- Any proved scheduler semantics now applies to the ascending binary input
array, with the exact verified radix conversion time added to the clock. -/
theorem run_realizes [DecidableEq P] {S T : Type*}
    (scheduler : FiniteRoutine (EvaluatorDigitFetch.Port P)) (e : Fin t → BurstRAM.Word Z)
    (d : List Bool) (hq : 2 ≤ TapeWord.value d) (payload : S → Stacks P)
    {post : T → Stacks (EvaluatorDigitFetch.Port P)} {B : ℕ} {effect : (T → ℕ) → S → ℕ}
    (h : Realizes scheduler.body
      (fun x => EvaluatorDigitFetch.bank
        (EvaluatorRadixRows.packedTable d.length (TapeWord.value d) (List.ofFn e))
        t Z d.length 0 0 0 Z (payload x)) post B effect) :
    Realizes (run scheduler).body (initial e d ∘ payload) (extend Z d ∘ post)
      (convertTicks t Z d.length + B) effect := by
  let pre (x : S) := EvaluatorDigitFetch.bank
    (EvaluatorRadixRows.packedTable d.length (TapeWord.value d) (List.ofFn e))
    t Z d.length 0 0 0 Z (payload x)
  have prefixRun : Realizes convert.body (initial e d ∘ payload) (extend Z d ∘ pre)
      (convertTicks t Z d.length) (fun f x => f x) := by
    apply Realizes.of_runs (g := id)
    intro x
    exact ⟨_, le_rfl, convert_runs e d (payload x) hq⟩
  exact prefixRun.followedBy (realizes_sched scheduler Z d h)

end EvaluatorProgramInput

end VPVNP
end Computability
end OAI
