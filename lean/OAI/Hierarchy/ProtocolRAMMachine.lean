import Mathlib.Tactic.FinCases
import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.Hierarchy.TaggedShorterCheapCPU

namespace OAI
/-! # Closing the advised controller at its accepted-selector word -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ContinuationLink

variable {w : ℕ}

private def flagTail {regs p k : ℕ} (flag : Word w) (pc : Fin 3 ↪ Fin p) :
    Fin 3 → Instr w p (regs+1) k
  | 0 => .constant (Fin.last regs) flag (pc 1)
  | 1 => .readExternal (Fin.last regs) (Fin.last regs) (pc 2)
  | 2 => .returnState (Fin.last regs)

def machine (A : Procedure w) (flag : Word w) :
    Machine w (A.labels+3) (A.registers+1) A.slots :=
  close (A.block.reindex (Fin.castAddEmb 1) id) (0 : Fin 3)
    (flagTail (regs:=A.registers) flag) A.publicData

/-- Appending this concrete three-instruction tail preserves every output cell and
returns its acceptance word. The terminal instruction itself uses the next clock row. -/
theorem machine_run (A : Procedure w) (flag state : Word w) (m out : Memory w)
    (budget : ℕ) (exec : A.Exec m out budget) :
    let M := machine A flag
    ∃ t ≤ budget+2, ∃ done, advance M.program t (M.program.start state) m = some (done,out) ∧
      M.program.step done = .finish (some (out flag.val)) := by
  let M := machine A flag
  let pc (j : Fin 3) := Fin.natAdd A.labels j
  let reg : Fin (A.registers+1) := Fin.last A.registers
  have installed := close_installed (A.block.reindex (Fin.castAddEmb 1) id) (0:Fin 3)
    (flagTail (regs:=A.registers) flag) A.publicData
  obtain ⟨t,bound,c,after,ran,entry,post⟩ := exec M (Fin.castAddEmb 3)
    (Fin.castAddEmb 1) id (pc 0) installed (fun _=>rfl) (M.program.start state) m rfl rfl
  subst after
  have rom (j : Fin 3) : M.code (pc j) = flagTail (regs:=A.registers) flag
      (Fin.natAddEmb A.labels) j := close_tail ..
  let mid := c.put (pc 1) reg flag
  let done := mid.put (pc 2) reg (out flag.val)
  have finalSteps : advance M.program 2 c out = some (done,out) := by
    simp [advance,Machine.program,entry,rom,flagTail,Instr.run,Config.put,mid,done,pc,reg]
  have halt : M.program.step done = .finish (some (out flag.val)) := by
    simp [Machine.program,done,mid,Config.put,rom,flagTail,Instr.run,reg,pc]
  exact ⟨t+2,by omega,done,advance_trans ran finalSteps,halt⟩

theorem machine_cheap (A : Procedure w) (flag : Word w)
    (cheap : ∀ {P R K : ℕ} (pc : Fin A.labels ↪ Fin P) (reg : Fin A.registers ↪ Fin R)
      (pub : Fin A.slots → Fin K) (exit : Fin P) (i : Fin A.labels),
      TaggedShorterCheapCPU.Cheap (A.block.emit pc reg pub exit i)) :
    ∀ pc, TaggedShorterCheapCPU.Cheap ((machine A flag).code pc) := by
  intro i
  induction i using Fin.addCases with
  | left j =>
    simp only [machine,close,Fin.addCases_left,Block.reindex]
    exact cheap _ _ _ _ j
  | right j =>
    simp only [machine,close,Fin.addCases_right]
    fin_cases j <;> trivial


end Hierarchy.ProtocolRAM

end OAI
