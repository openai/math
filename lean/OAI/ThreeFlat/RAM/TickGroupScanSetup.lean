import OAI.ThreeFlat.RAM.DeterministicBlock
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # Initializing the native group scan from the physical tick cache -/

namespace ThreeFlat.RAM.TickGroupScanSetup

open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- The three cached values are the actual number of bucket descriptors,
the phase's physical chunk offset, and the decoded history group. -/
structure Addresses where
  table : ℕ
  countAddr : ℕ
  chunkAddr : ℕ
  groupAddr : ℕ
  mapBase : ℕ
  bits : ℕ

def emit (A : Addresses) (P : Fin 13 → Fin p) (R : Fin 15 ↪ Fin r) (exit : Fin p) :
    Fin 13 → Instr w p r k
  | 0 => .constant (R 0) (A.table : Word w) (P 1)
  | 1 => .constant (R 1) (A.countAddr : Word w) (P 2)
  | 2 => .readExternal (R 1) (R 1) (P 3)
  | 3 => .constant (R 7) 4 (P 4)
  | 4 => .binary .mul (R 1) (R 1) (R 7) (P 5)
  | 5 => .binary .add (R 1) (R 0) (R 1) (P 6)
  | 6 => .constant (R 2) (A.chunkAddr : Word w) (P 7)
  | 7 => .readExternal (R 2) (R 2) (P 8)
  | 8 => .constant (R 3) (A.bits : Word w) (P 9)
  | 9 => .binary .add (R 3) (R 2) (R 3) (P 10)
  | 10 => .constant (R 4) (A.mapBase : Word w) (P 11)
  | 11 => .constant (R 5) (A.groupAddr : Word w) (P 12)
  | _ => .readExternal (R 5) (R 5) exit

theorem advance_setup (A : Addresses) (M : Machine w p r k) (P : Fin 13 → Fin p)
    (R : Fin 15 ↪ Fin r) (exit : Fin p) (rom : ∀ i, M.code (P i) = emit A P R exit i)
    (c : Config w p r) (m : Memory w) (entry : c.pc = P 0) :
    ∃ out : Config w p r, advance M.program 13 c m = some (out,m) ∧ out.pc = exit ∧
      out.reg (R 0) = (A.table : Word w) ∧
      out.reg (R 1) = (A.table : Word w)+m (A.countAddr : Word w).val*4 ∧
      out.reg (R 2) = m (A.chunkAddr : Word w).val ∧
      out.reg (R 3) = m (A.chunkAddr : Word w).val+(A.bits : Word w) ∧
      out.reg (R 4) = (A.mapBase : Word w) ∧ out.reg (R 5) = m (A.groupAddr : Word w).val := by
  simp (config:={decide:=true}) [advance,Machine.program,entry,rom,emit,Instr.run,
    Config.put,Function.update,R.injective.eq_iff,BinaryOp.eval]

end ThreeFlat.RAM.TickGroupScanSetup

end OAI
