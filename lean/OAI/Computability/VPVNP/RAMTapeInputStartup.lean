import OAI.Computability.VPVNP.RAMTapeInput
import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.RAMTapeNamed

/-!
# Sequencing input measurement, public parameters and field parsing

The raw input starts on one stack and all remaining stacks start empty. The
fixed length pass restores the input, the parameter pass computes the two
field widths, and the fixed parsing pass extracts the four data stacks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.InputReader

open BurstRAM ProcessorInput RAMLayout UniversalMachine StackCompiler

variable {K : Type} [DecidableEq K]

/-- The input registers together with the parameter routine's scratch bank. -/
def withScratch (s : Stacks InputPort) : Stacks (InputPort ⊕ K) := Sum.elim s (fun _ => [])

/-- The complete physical tape has been measured and restored. -/
def measured (raw : List Bool) (n : ℕ) : Stacks (InputPort ⊕ K) :=
  withScratch (prepared raw 0 0 (List.replicate n true))

/-- Measure and restore the raw input, prepare its field widths with the supplied routine, and
parse the site fields. -/
def startup (parameters : FiniteRoutine (InputPort ⊕ K)) :=
  (((FiniteRoutine.ofRoutine lengthRoutine).onPorts Sum.inl).followedBy parameters).followedBy
    ((FiniteRoutine.ofRoutine parse).onPorts Sum.inl)

omit [DecidableEq K] in
private theorem length_start (raw : List Bool) :
    lengthRoutine.Runs (5*raw.length+2) (prepared raw 0 0 [])
      (prepared raw 0 0 (List.replicate raw.length true)) := by
  have h := lengthRoutine_runs (prepared raw 0 0 []) rfl
  change lengthRoutine.Runs (5*raw.length+2) _ (Function.update _ .size (List.replicate raw.length true ++ [])) at h
  rw [List.append_nil] at h
  have he : Function.update (prepared raw 0 0 []) .size (List.replicate raw.length true) =
      prepared raw 0 0 (List.replicate raw.length true) := by funext j; cases j <;> rfl
  exact he ▸ h

/-- The raw site tape is the only populated stack at entry. Once the public
parameter pass has run on its measured size, parsing incurs at most another
`5n+17` stack instructions. -/
theorem startup_runs (params : FiniteRoutine (InputPort ⊕ K)) {d H w : ℕ}
    (p : UniversalMachine.Program) (n : ℕ) (v : Fin (2^d)) (hdr : Header) (inc : Fin (width d H w) → Bool)
    (hf : Fits p n d H w) (t : ℕ)
    (hp : params.Runs t (measured (ProcessorInput.tape p n v hdr inc) n)
      (withScratch (prepared (ProcessorInput.tape p n v hdr inc) d (width d H w) []))) :
    let raw := ProcessorInput.tape p n v hdr inc
    let small := prepared raw d (width d H w) []
    ∃ steps ≤ t + 10*n+19, (startup params).Runs steps (labeledInput (.inl InputPort.input) raw)
      (withScratch (result small (programPrefix p)
        (List.ofFn (RAMSerialization.wordBits d v)) (List.ofFn hdr) (List.ofFn inc))) := by
  let raw := ProcessorInput.tape p n v hdr inc
  let small := prepared raw d (width d H w) []
  have hlen : raw.length = n := ProcessorInput.length_tape p v hdr inc hf
  have hm := length_start raw
  rw [hlen] at hm
  have hmeasure : ((FiniteRoutine.ofRoutine lengthRoutine).onPorts Sum.inl).Runs (5*n+2)
      (labeledInput (.inl InputPort.input) raw) (measured (K := K) raw n) :=
    (FiniteRoutine.ofRoutine lengthRoutine).runs_onPorts_framed Sum.inl_injective hm
      (fun i => by cases i <;> rfl) (fun _ => rfl) (fun j hj => by
        cases j with
        | inl i => exact (hj i rfl).elim
        | inr _ => rfl)
  obtain ⟨z, hz, hparse⟩ := parse_processorTape p n v hdr inc [] hf
  let done := result small (programPrefix p) (List.ofFn (RAMSerialization.wordBits d v)) (List.ofFn hdr) (List.ofFn inc)
  have hread : ((FiniteRoutine.ofRoutine parse).onPorts Sum.inl).Runs z
      (withScratch (K := K) small) (withScratch done) :=
    (FiniteRoutine.ofRoutine parse).runs_onPorts_framed Sum.inl_injective hparse
      (fun _ => rfl) (fun _ => rfl) (fun j hj => by
        cases j with
        | inl i => exact (hj i rfl).elim
        | inr _ => rfl)
  exact ⟨_, by omega, (hmeasure.followedBy hp).followedBy hread⟩

end RAMTape.InputReader

end VPVNP
end Computability
end OAI
