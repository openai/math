import OAI.Computability.VPVNP.RAMTapeMapWord
import Mathlib.Tactic.DeriveFintype

/-!
# Record buffer word registers

The pre-sort probe records are accumulated in reverse bit order. Copying a
staged word into the buffer restores the source using one scratch stack.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.RecordBuffer

/-- The five staged word fields, temporary copy stack, reverse buffer, free-slot counter,
zeros, and output of the record emitter. -/
inductive Port
  | field (i : Fin 5)
  | temp | reverseBuffer | remaining | zeros | output
  deriving DecidableEq, Fintype

/-- Copy one staged word into the reverse record buffer, restoring the source word afterward. -/
def appendWord (src : Port) : FiniteRoutine Port :=
  WordCopy.mapWord .temp .reverseBuffer id src

theorem appendWord_run {src : Port} (h₁ : src ≠ .temp) (h₂ : src ≠ .reverseBuffer)
    (s : Stacks Port) (ht : s .temp = []) :
    (appendWord src).Runs (5*(s src).length+2) s
      (Function.update s .reverseBuffer ((s src).reverse ++ s .reverseBuffer)) := by
  simpa [appendWord] using WordCopy.mapWord_run .temp .reverseBuffer id h₁ h₂ (by decide) s ht

end RAMTape.RecordBuffer

end VPVNP
end Computability
end OAI
