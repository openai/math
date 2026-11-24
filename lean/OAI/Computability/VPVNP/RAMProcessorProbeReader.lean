import OAI.Computability.VPVNP.RAMProcessorProbeFields
import OAI.Computability.VPVNP.RAMProcessorReadWord
import OAI.Computability.VPVNP.RAMProcessorFlow

/-!
# External read guesses on the architectural processor bank

The source address word supplies the width. The guessed value is placed in
the independent record-value field, so its bits cannot overwrite an aliased
address register before the address is recorded. A short stream exits in
rejection at the first missing bit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ProbeStages

open BurstRAM

variable {r k w : ℕ}

private def readPorts (addr : Fin r) : ProbeWord.Port → Port r k
  | .template => .inl (.reg addr)
  | .stream => .inr .choices
  | .value => .inr .value
  | .saved => .inr .copyA
  | .bits => .inr .copyB

private theorem read_inj (addr : Fin r) : Function.Injective (readPorts (k := k) addr) := by
  intro i j h
  cases i <;> cases j <;> simp_all [readPorts]

private def readerExits : ProbeWord.State → Option Bool
  | .done => some true
  | .reject => some false
  | _ => none

private theorem reader_active (q : ProbeWord.State) (h : (ProbeWord.code q).returns = false) :
    readerExits q = none := by cases q <;> first | rfl | contradiction

/-- Read as many private choice bits as there are bits in the address register and stage the
resulting word. The Boolean exit reports whether the entire word was available. -/
def reader (addr : Fin r) : Fragment (Port r k) Bool :=
  (Fragment.fromCode ProbeWord.code .clear readerExits).onPorts (readPorts addr)

private theorem frame (s : Bank r k) (addr : Fin r) (choices value : List Bool) :
    installStacks (readPorts addr) s.stacks (ProbeWord.bank (s.isa (.reg addr)) choices value [] []) =
      ({s with choices, value} : Bank r k).stacks := by
  apply installStacks_frame (read_inj addr)
  · intro i; cases i <;> rfl
  · intro i hi
    rcases i with j | j
    · rfl
    · cases j <;> first | rfl | exact (hi .stream rfl).elim | exact (hi .value rfl).elim

/-- Complete-word input preserves the address and leaves the exact unused
choice suffix. Width zero consumes no choice bits. -/
theorem reader_run (addr : Fin r) (s : Bank r k) (a v : Word w) (tail : List Bool)
    (ha : s.isa (.reg addr) = wordBits a) (hs : s.choices = wordBits v ++ tail) :
    (reader addr).Runs (s.value.length+8*w+4) s.stacks true
      ({s with choices := tail, value := wordBits v} : Bank r k).stacks := by
  have h := ProbeWord.read_run (wordBits a) (wordBits v) tail s.value (by simp)
  rw [length_wordBits, ← hs, ← ha] at h
  have localRun := Fragment.fromCode_runs readerExits rfl rfl reader_active h
  have installed := Fragment.runs_onPorts (readPorts addr) (read_inj addr) s.stacks localRun
  rwa [frame, frame] at installed

/-- Short-word input reaches the rejecting exit without dispatching any
following instruction. The contents of that rejected branch need no rewind. -/
theorem reader_short (addr : Fin r) (s : Bank r k) (a : Word w)
    (ha : s.isa (.reg addr) = wordBits a) (hs : s.choices.length < w) :
    ∃ out, (reader addr).Runs (s.value.length+4*s.choices.length+3) s.stacks false out := by
  obtain ⟨out, run⟩ := ProbeWord.short_run (wordBits a) s.choices s.value (by simpa using hs)
  rw [← ha] at run
  have localRun := Fragment.fromCode_runs readerExits rfl rfl reader_active run
  have installed := Fragment.runs_onPorts (readPorts addr) (read_inj addr) s.stacks localRun
  rw [frame] at installed
  exact ⟨_, installed⟩

end RAMTape.ProbeStages

end VPVNP
end Computability
end OAI
