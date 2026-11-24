import OAI.Computability.VPVNP.RAMTapeCoefficient
import OAI.Computability.VPVNP.RAMTapeStackLift

/-!
# Named stack ports for the literal coefficient machine

Port zero receives the raw input tape. All other labels in the finite bank
are sent to distinct positive ports, so a program can be compiled directly
from its named stack control. Renaming preserves each branch's halting bound
and the integer count of accepting paths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

/-- Relabel a finite-control machine with all instructions preserved,
including both targets of each binary choice. -/
theorem stopsWithin_lift {K L Q R : Type*} [DecidableEq K] [DecidableEq L]
    {src : StackCode K Q} {target : StackCode L R} (ports : K → L)
    (hp : Function.Injective ports) (labels : Q → R) (base : Stacks L)
    (hc : ∀ q, target (labels q) = (src q).rename ports labels)
    (n : ℕ) (q : Q) (s : Stacks K) :
    StopsWithin target n (labels q) (installStacks ports base s) ↔ StopsWithin src n q s := by
  induction n generalizing q s with
  | zero => rfl
  | succ n ih =>
    rw [StopsWithin, hc, StopsWithin]
    cases src q <;> simp only [StackOp.rename, Function.comp_apply, installStacks_at hp,
      installStacks_update hp, ih]

namespace StackCompiler

open UniversalMachine BurstRAM

variable {K Q : Type*} [Fintype K] [DecidableEq K]

/-- The physical compiler uses a spare positive port to avoid subtracting
one from the bank size when moving the designated input to port zero. -/
noncomputable def labeledPort (inputPort p : K) : Fin (Fintype.card K + 1) :=
  if p = inputPort then 0 else (Fintype.equivFin K p).succ

theorem labeledPort_injective (inputPort : K) : Function.Injective (labeledPort inputPort) := by
  intro i j h
  by_cases hi : i = inputPort <;> by_cases hj : j = inputPort <;>
    simp_all [labeledPort, Fin.succ_inj]
  exact (Fin.succ_ne_zero _ h.symm).elim

/-- Relocate the named stack instructions to numerical stack indices. -/
noncomputable def labeledCode (inputPort : K) (code : StackCode K Q) : StackCode (Fin (Fintype.card K + 1)) Q :=
  fun q => (code q).rename (labeledPort inputPort) id

/-- Initialize the designated input stack with the raw input word. -/
def labeledInput (inputPort : K) (raw : Word) : Stacks K :=
  fun p => if p = inputPort then raw else []

theorem installedInput (inputPort : K) (raw : Word) :
    installStacks (labeledPort inputPort) (inputStacks raw) (labeledInput inputPort raw) = inputStacks raw := by
  apply installStacks_eq (labeledPort_injective inputPort)
  intro p
  by_cases h : p = inputPort <;> simp [h, labeledPort, labeledInput, inputStacks]

variable [Fintype Q]

/-- The literal universal-machine program for the named stack machine. -/
noncomputable abbrev labeledProgram (inputPort : K) (code : StackCode K Q) (start : Q) : Program :=
  program (labeledCode inputPort code) start

/-- The fixed two-tape table for a labeled stack program computes its exact
bounded accepting-path count from a raw input. -/
theorem input_count_labeled (inputPort : K) (code : StackCode K Q) (start : Q) (raw : Word)
    (T ticks : ℕ) (stops : StopsWithin code T start (labeledInput inputPort raw))
    (clock : T * (6 * (raw.length + (Fintype.card K + 1) + T) + 4) ≤ ticks) :
    paths (labeledProgram inputPort code start) ticks (initial (labeledProgram inputPort code start) raw) =
      stackPaths code T start (labeledInput inputPort raw) := by
  have halt := (stopsWithin_lift (target := labeledCode inputPort code) (labeledPort inputPort)
    (labeledPort_injective inputPort) id (inputStacks raw) (fun _ => rfl) T start _).2 stops
  have count := stackPaths_lift (src := code) (target := labeledCode inputPort code) (labeledPort inputPort)
    (labeledPort_injective inputPort) id (inputStacks raw) (fun _ => rfl) T start (labeledInput inputPort raw)
  rw [installedInput] at halt count
  exact (input_count _ _ _ _ _ halt clock).trans count

/-- At a site, the input on the designated named port contains the fixed
program's own prefix, header, incidence messages, and padding to length n. -/
theorem site_count_labeled (inputPort : K) (code : StackCode K Q) (start : Q) (n T : ℕ) {d H w : ℕ}
    (v : Fin (2^d)) (hdr : ProcessorInput.Header) (inc : Fin (RAMLayout.width d H w) → Bool)
    (fits : ProcessorInput.Fits (labeledProgram inputPort code start) n d H w)
    (stops : StopsWithin code T start (labeledInput inputPort
      (ProcessorInput.tape (labeledProgram inputPort code start) n v hdr inc)))
    (clock : T * (6 * (n + (Fintype.card K + 1) + T) + 4) ≤ n^clockExponent) :
    acceptingCount (ProcessorInput.encode (labeledProgram inputPort code start) n v hdr inc fits) =
      stackPaths code T start (labeledInput inputPort
        (ProcessorInput.tape (labeledProgram inputPort code start) n v hdr inc)) := by
  rw [ProcessorInput.coefficient]
  apply input_count_labeled _ _ _ _ _ _ stops
  simpa only [ProcessorInput.length_tape _ _ _ _ fits] using clock

end StackCompiler
end RAMTape

end VPVNP
end Computability
end OAI
