import Mathlib.Data.Fin.VecNotation
import OAI.ThreeFlat.RAM.PhysicalProcedure

namespace OAI
/-! # Scalar literal writes in a native continuation -/

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.ContinuationLink
variable {W : ℕ}

def skip : Procedure W :=
  ⟨1,1,0,{first := 0, emit := fun _ r _ exit _ => .constant (r 0) 0 exit},Fin.elim0⟩

theorem skip_spec : (skip : Procedure W).Spec (fun _=>True) (fun m o=>o=m) 1 := by
  intro n r k M pc reg pub exit inst words c m entry _
  change Fin 1 ↪ Fin n at pc
  change Fin 1 ↪ Fin r at reg
  change c.pc=pc 0 at entry
  have code : M.code (pc 0)=.constant (reg 0) 0 exit := inst (0 : Fin 1)
  refine ⟨1,le_rfl,c.put exit (reg 0) 0,m,?_,rfl,rfl⟩
  simp [advance,Machine.program,entry,code,Instr.run]

def start (cell : Word W) (value : Word W) : Procedure W :=
  ⟨3,2,0,{first := 0, emit := fun pc r _ exit =>
    ![.constant (r 0) cell (pc 1),.constant (r 1) value (pc 2),.writeExternal (r 0) (r 1) exit]},Fin.elim0⟩

theorem start_spec (cell value : Word W) :
    (start cell value).Spec (fun _=>True) (fun m o=>o=writeMemory m cell value) 3 := by
  intro n r k M pc reg pub exit inst data c m entry _
  change Fin 3 ↪ Fin n at pc
  change Fin 2 ↪ Fin r at reg
  let d := (c.put (pc 1) (reg 0) cell).put (pc 2) (reg 1) value
  refine ⟨3,le_rfl,{d with pc:=exit},writeMemory m cell value,?_,rfl,rfl⟩
  change c.pc=pc 0 at entry
  have rom (i : Fin 3) : M.code (pc i) =
      (![.constant (reg 0) cell (pc 1),.constant (reg 1) value (pc 2),
        .writeExternal (reg 0) (reg 1) exit] : Fin 3→Instr W n r k) i := inst i
  simp (config := {decide:=true}) [advance,Machine.program,entry,rom,Instr.run,Config.put,d]

end ThreeFlat.Diagonal.NavigationPass

end OAI
