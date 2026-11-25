import OAI.Computability.VPVNP.RAMExecution
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Finset.Card

namespace OAI
/-! # Natural-address state of the physical first-passage scan -/

namespace Hierarchy.GridPassageRAMRow
open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing

/-- A row writes its chosen index and increments its cell counter precisely when the
passage is untouched and its cell/direction still needs another catalyst. Every row writes its mark. -/
def natStep {w : ℕ} (counterBase chosenBase markBase B key rail i : ℕ) (untouched : Bool)
    (m : Memory w) : Memory w :=
  let old := (m (counterBase+key)).val
  if untouched = true ∧ old < B then
    Function.update (Function.update (Function.update m (chosenBase+key*B+old) (rail : Word w))
      (counterBase+key) ((old+1 : ℕ) : Word w)) (markBase+i) 1
  else Function.update m (markBase+i) 0

/-- Within the word address space the native write is a single natural-address update. -/
theorem writeMemory_nat {w addr : ℕ} (m : Memory w) (v : Word w) (h : addr < 2^w) :
    writeMemory m (addr : Word w) v = Function.update m addr v := by
  funext i
  by_cases eq : i = addr <;> simp [writeMemory, eq, Fin.val_cast_of_lt h, Function.update]

end Hierarchy.GridPassageRAMRow

end OAI
