import OAI.ThreeFlat.RAM.PhysicalProcedure
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases

namespace OAI
/-! # Advance the persistent stage-info pointer after successful admission and publication -/

namespace ThreeFlat.RAM.NextStage

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink PhysicalProcedure
open scoped Fin.CommRing
variable {w p r k : ℕ}

def block (cell : Word w) : Block w 6 3 0 where
  first := 0
  emit pc r _ halt := ![.constant (r 0) cell (pc 1), .readExternal (r 1) (r 0) (pc 2),
    .constant (r 2) 4 (pc 3), .binary .add (r 1) (r 1) (r 2) (pc 4),
    .readExternal (r 1) (r 1) (pc 5), .writeExternal (r 0) (r 1) halt]

def procedure (cell : Word w) : Procedure w := ⟨6,3,0,block cell,Fin.elim0⟩

theorem run (cell : Word w) (M : Machine w p r k) (pc : Fin 6 ↪ Fin p) (reg : Fin 3 ↪ Fin r)
    (pub : Fin 0 → Fin k) (exit : Fin p) (inst : (block cell).Installed M pc reg pub exit)
    (c : Config w p r) (m : Memory w) (start : c.pc=pc 0) :
    ∃ d, advance M.program 6 c m=some (d,writeMemory m cell (m (m cell.val+4).val)) ∧ d.pc=exit := by
  let d := ((((c.put (pc 1) (reg 0) cell).put (pc 2) (reg 1) (m cell.val)).put (pc 3) (reg 2) 4).put
    (pc 4) (reg 1) (m cell.val+4)).put (pc 5) (reg 1) (m (m cell.val+4).val)
  have row (i : Fin 6) : M.code (pc i)=(block cell).emit pc reg pub exit i := inst i
  refine ⟨{d with pc:=exit},?_,rfl⟩
  simp (config := {decide := true}) [advance,Machine.program,start,row,block,Instr.run,BinaryOp.eval,Config.put,d,
    Function.update_idem]

end ThreeFlat.RAM.NextStage

end OAI
