import Mathlib.Tactic.FinCases
import OAI.ThreeFlat.RAM.DeterministicBlock
import OAI.ThreeFlat.Diagonal.TickAuxiliary
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Caching decoded identifiers, phase, and shared branch marker -/

namespace ThreeFlat.RAM.TickControlHeader
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickChronology Diagonal.TickAuxiliary

variable {w k p r : ℕ}

/-- The opening reads the proposed marker. Every later transition reads its
old marker, even on the closing transition that clears it. -/
def markerAddr (q : Phase) (old new : Word w) : Word w := if q = .opening then new else old

/-- Regs zero through two already hold team, step and phase. The two
remaining scratch registers can contain arbitrary words. -/
def emit (P : Fin 10 → Fin p) (R : Fin 5 → Fin r) (dest : Fin 4 → Word w)
    (marker : Word w) (exit : Fin p) : Fin 10 → Instr w p r k
  | 0 => .constant (R 3) marker (P 1)
  | 1 => .readExternal (R 4) (R 3) (P 2)
  | 2 => .constant (R 3) (dest 0) (P 3)
  | 3 => .writeExternal (R 3) (R 0) (P 4)
  | 4 => .constant (R 3) (dest 1) (P 5)
  | 5 => .writeExternal (R 3) (R 1) (P 6)
  | 6 => .constant (R 3) (dest 2) (P 7)
  | 7 => .writeExternal (R 3) (R 2) (P 8)
  | 8 => .constant (R 3) (dest 3) (P 9)
  | _ => .writeExternal (R 3) (R 4) exit

def store (dest : Fin 4 → Word w) (vals : Fin 4 → Word w) (m : Memory w) : Memory w :=
  writeMemory (writeMemory (writeMemory (writeMemory m (dest 0) (vals 0))
    (dest 1) (vals 1)) (dest 2) (vals 2)) (dest 3) (vals 3)

theorem store_read (dest : Fin 4 ↪ Word w) (vals : Fin 4 → Word w) (m : Memory w) (i : Fin 4) :
    store dest vals m (dest i).val = vals i := by
  have eq (x y : Fin 4) : (dest x).val = (dest y).val ↔ x=y := Fin.val_injective.eq_iff.trans dest.injective.eq_iff
  fin_cases i <;> simp [store,writeMemory,eq]

theorem store_outside (dest : Fin 4 → Word w) (vals : Fin 4 → Word w) (m : Memory w) (j : ℕ)
    (outside : ∀ i, j ≠ (dest i).val) : store dest vals m j = m j := by
  simp only [store,writeMemory,ite_eq_right (outside _)]

/-- Ten instructions write the control header without reading a descriptor,
altering the persistent state, or modifying a private word. -/
theorem advance_header (M : Machine w p r k) (P : Fin 10 → Fin p) (R : Fin 5 ↪ Fin r)
    (dest : Fin 4 → Word w) (marker : Word w) (exit : Fin p)
    (rom : ∀ i, M.code (P i) = emit P R dest marker exit i)
    (c : Config w p r) (m : Memory w) (start : c.pc = P 0) :
    ∃ out : Config w p r, out.pc = exit ∧
      (∀ i : Fin 3, out.reg (R (i.castAdd 2)) = c.reg (R (i.castAdd 2))) ∧
      out.persistent = c.persistent ∧ out.privateMem = c.privateMem ∧
      advance M.program 10 c m = some (out,
        store dest ![c.reg (R 0), c.reg (R 1), c.reg (R 2), m marker.val] m) := by
  let d := (((((c.put (P 1) (R 3) marker).put (P 2) (R 4) (m marker.val)).put
    (P 3) (R 3) (dest 0)).put (P 5) (R 3) (dest 1)).put (P 7) (R 3) (dest 2)).put
    (P 9) (R 3) (dest 3)
  refine ⟨{d with pc := exit},rfl,?_,rfl,rfl,?_⟩
  · intro i
    fin_cases i <;> simp [d, Config.put, Function.update,R.injective.eq_iff]
  · simp [advance,Machine.program,start,rom,emit,Instr.run,Config.put,Function.update,R.injective.eq_iff,store,d]

end ThreeFlat.RAM.TickControlHeader

end OAI
