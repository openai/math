import OAI.Computability.VPVNP.RAMTapeStackClock
import OAI.Computability.VPVNP.RAMSiteInput
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Fixed bit-stack processors as literal coefficients of the integer family

The original raw input is already the contents of stack zero. The blank tail
of that tape supplies the separators of every unused stack. Consequently the
table reads its own prefix in exactly the same way as any subsequent bit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.StackCompiler

open UniversalMachine Turing BurstRAM

variable {k : ℕ} {Q : Type*} [Fintype Q]

/-- The concrete universal-machine program that simulates the indexed stack code. -/
noncomputable abbrev program (code : StackCode (Fin (k+1)) Q) (start : Q) : Program :=
  compile (.ready start) (rows code)

/-- Put the input word on the first stack and initialize the others to empty. -/
def inputStacks (input : Word) : Stacks (Fin (k+1)) := Fin.cons input (fun _ => [])

private theorem empty_fields (n : ℕ) : fields (List.replicate n []) = List.replicate n 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem packed_input (input : Word) :
    packed (inputStacks (k := k) input) = input.map bit ++ List.replicate (k+1) 0 := by
  simp [packed, inputStacks, List.ofFn_succ, empty_fields, List.replicate_succ]

theorem physical_initial (code : StackCode (Fin (k+1)) Q) (start : Q) (input : Word) :
    initial (program code start) input = running (.ready start) (.ready start)
      (tapeList (packed (inputStacks (k := k) input))) (tapeList []) := by
  rw [initial_eq_running, packed_input]
  have he : ListBlank.mk (input.map bit ++ List.replicate (k+1) 0) = ListBlank.mk (input.map bit) :=
    Quotient.sound (Or.inr ⟨k+1, rfl⟩)
  exact congrArg (fun r => running (Phase.ready (k := k+1) start) (.ready start) (Tape.mk' (ListBlank.mk []) r) (tapeList [])) he.symm

theorem input_count (code : StackCode (Fin (k+1)) Q) (start : Q) (input : Word) (T ticks : ℕ)
    (stops : StopsWithin code T start (inputStacks input))
    (clock : T * (6 * (input.length + (k+1) + T) + 4) ≤ ticks) :
    paths (program code start) ticks (initial (program code start) input) =
      stackPaths code T start (inputStacks input) := by
  rw [physical_initial]
  apply physical_eq code start T start _ _ ticks stops _ clock
  simp [packed_input]

/-- The same prefix serves every length and every payload that fits the
clock. All branch counts include the literal table's prefix in the input. -/
theorem prefix_count (code : StackCode (Fin (k+1)) Q) (start : Q) (payload : Word) (T : ℕ)
    (stops : StopsWithin code T start (inputStacks (programPrefix (program code start) ++ payload)))
    (clock : let n := (programPrefix (program code start)).length + payload.length
      T * (6 * (n + (k+1) + T) + 4) ≤ n^clockExponent) :
    acceptingCount ((programPrefix (program code start) ++ payload).get) =
      stackPaths code T start (inputStacks (programPrefix (program code start) ++ payload)) := by
  simp only [acceptingCount, List.ofFn_get, decode_programPrefix]
  apply input_count _ _ _ _ _ stops
  simpa only [List.length_append] using clock

/-- The processor receives exactly its local fields and the shared prefix
under the length-`n` site encoding used by the contraction. -/
theorem site_count (code : StackCode (Fin (k+1)) Q) (start : Q) (n T : ℕ) {d H w : ℕ}
    (v : Fin (2^d)) (hdr : ProcessorInput.Header) (inc : Fin (RAMLayout.width d H w) → Bool)
    (fits : ProcessorInput.Fits (program code start) n d H w)
    (stops : StopsWithin code T start (inputStacks (ProcessorInput.tape (program code start) n v hdr inc)))
    (clock : T * (6 * (n + (k+1) + T) + 4) ≤ n^clockExponent) :
    acceptingCount (ProcessorInput.encode (program code start) n v hdr inc fits) =
      stackPaths code T start (inputStacks (ProcessorInput.tape (program code start) n v hdr inc)) := by
  rw [ProcessorInput.coefficient]
  apply input_count _ _ _ _ _ stops
  simpa only [ProcessorInput.length_tape _ _ _ _ fits] using clock

end RAMTape.StackCompiler

end VPVNP
end Computability
end OAI
