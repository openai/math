import OAI.Hierarchy.CheapISAMachine

namespace OAI
/-! # Native execution of all ten continuing instruction handlers -/

namespace Hierarchy.CheapISA
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing

namespace Body

variable {w p r : ℕ}

def label (op : Fin 10) : Fin 72 := ![49,50,51,52,53,54,55,56,57,60] op

def ticks (op : Fin 10) : ℕ := ![3,3,3,5,5,3,2,2,5,4] op

theorem ticks_le (op : Fin 10) : ticks op ≤ 5 := by fin_cases op <;> decide

def dataAddress (p r : ℕ) (d : Config (width w) 72 13) : Word (width w) :=
  (dataBase p r : Word _) + d.reg 8

def result (p r : ℕ) (op : Fin 10) (d : Config (width w) 72 13)
    (m : Memory (width w)) : Word (width w) :=
  match op.val with
  | 0 => d.reg 2
  | 1 => d.persistent
  | 2 => d.reg 8
  | 3 => BinaryOp.bitAnd.eval (d.reg 8+d.reg 9) (mask w)
  | 4 => BinaryOp.bitAnd.eval (d.reg 8-d.reg 9) (mask w)
  | 5 => BinaryOp.bitAnd.eval (d.reg 8) (d.reg 9)
  | _ => m (dataAddress p r d).val

def next (op : Fin 10) (d : Config (width w) 72 13) : Word (width w) :=
  match op.val with
  | 6 => if d.reg 8=d.reg 9 then d.reg 6 else d.reg 7
  | 7 => if d.reg 8<d.reg 9 then d.reg 6 else d.reg 7
  | _ => d.reg 6

def memory (p r : ℕ) (op : Fin 10) (d : Config (width w) 72 13)
    (m : Memory (width w)) : Memory (width w) :=
  match op.val with
  | 6 | 7 => m
  | 9 => writeMemory m (dataAddress p r d) (d.reg 9)
  | _ => writeMemory m (d.reg 5) (result p r op d m)

private theorem resultOf {P : Program (width w) (Config (width w) 72 13)}
    {t : ℕ} {d : Config (width w) 72 13} {n o : Memory (width w)} {pc : Word (width w)}
    (computed : match advance P t d n with
      | none => False
      | some (e,actual) => actual=o ∧ e.pc=1 ∧ e.reg 0=pc ∧ e.persistent=d.persistent) :
    ∃e,advance P t d n=some (e,o) ∧ e.pc=1 ∧ e.reg 0=pc ∧ e.persistent=d.persistent := by
  cases ex : advance P t d n with
  | none => rw [ex] at computed; exact False.elim computed
  | some pair =>
    obtain ⟨e,f⟩:=pair
    rw [ex] at computed
    obtain ⟨same,entry,read,held⟩:=computed
    subst f
    exact ⟨e,rfl,entry,read,held⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
/-- Native witnesses return to the fetch instruction. A register write and a data
write each issue one real external store; a conditional branch issues neither store. -/
theorem run (entry : Fin p) (op : Fin 10) (d : Config (width w) 72 13)
    (n : Memory (width w)) (pc : d.pc=label op) :
    ∃e,advance (machine w p r entry).program (ticks op) d n =
      some (e,memory p r op d n) ∧ e.pc=1 ∧ e.reg 0=next op d ∧ e.persistent=d.persistent := by
  apply resultOf
  fin_cases op
  · change d.pc=49 at pc
    simp [advance,Machine.program,machine,pc,code,Instr.run,Config.put,
      Function.update,BinaryOp.eval,memory,result,ticks,next]
  · change d.pc=50 at pc
    simp [advance,Machine.program,machine,pc,code,Instr.run,Config.put,
      Function.update,BinaryOp.eval,memory,result,ticks,next]
  · change d.pc=51 at pc
    simp [advance,Machine.program,machine,pc,code,Instr.run,Config.put,
      Function.update,BinaryOp.eval,memory,result,ticks,next]
  · change d.pc=52 at pc
    simp [advance,Machine.program,machine,pc,code,Instr.run,Config.put,
      Function.update,BinaryOp.eval,memory,result,ticks,next]
  · change d.pc=53 at pc
    simp [advance,Machine.program,machine,pc,code,Instr.run,Config.put,
      Function.update,BinaryOp.eval,memory,result,ticks,next]
  · change d.pc=54 at pc
    simp [advance,Machine.program,machine,pc,code,Instr.run,Config.put,
      Function.update,BinaryOp.eval,memory,result,ticks,next]
  · change d.pc=55 at pc
    by_cases test : d.reg 8=d.reg 9 <;>
      simp [advance,Machine.program,machine,pc,code,Instr.run,Config.put,
        Function.update,BinaryOp.eval,memory,ticks,next,test]
  · change d.pc=56 at pc
    by_cases test : d.reg 8<d.reg 9 <;>
      simp [advance,Machine.program,machine,pc,code,Instr.run,Config.put,
        Function.update,BinaryOp.eval,memory,ticks,next,test]
  · change d.pc=57 at pc
    simp [advance,Machine.program,machine,pc,code,Instr.run,Config.put,
      Function.update,BinaryOp.eval,memory,result,dataAddress,ticks,next]
  · change d.pc=60 at pc
    simp [advance,Machine.program,machine,pc,code,Instr.run,Config.put,
      Function.update,BinaryOp.eval,memory,dataAddress,ticks,next]

end Body
end Hierarchy.CheapISA

end OAI
