import OAI.Computability.VPVNP.PrimedInputRAMOpcodeExecution

/-!
# The finite table for the two-pass input RAM

Four private instructions compare the persistent cursor with twice the public rectangle
size. At the terminal cursor they jump to accept. At each data cursor they jump into the
compiled input block, whose return instruction supplies the next cursor from register 29.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Opcodes

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

/-- Code for one data call. It loads parameters, decodes the cursor, resolves the incident port
when needed, and performs the scheduled action. -/
abbrev body := dataCall PortCode.program
/-- Number of instruction addresses in the input table, including its seven front instructions
and the data-call body. -/
abbrev pcCount := 7 + body.length

private def front (i : Fin 7) : Fin pcCount := Fin.castAdd body.length i

/-- Translate a data-call instruction label into its table address after the seven front
instructions. -/
def bodyLabel (i : body.Label) : Fin pcCount := Fin.natAdd 7 (body.labels i)

/-- Instruction address that returns register 29 as the next persistent cursor. -/
def returnPC := front 5
/-- Address of the input table's rejection instruction. -/
def badPC := front 6

private def beforeBody : Fin 7 → Instr 2 pcCount 48 16 :=
  ![.stateWord 4 (front 1), .publicWord 5 0 (front 2), .binary .add 30 5 5 (front 3),
    .jumpEq 4 30 (front 4) (bodyLabel body.entry), .accept, .returnState 29, .reject]

/-- The same opcode table works for all parameter lengths and word widths. -/
def inputTable : Template pcCount 48 16 where
  literalWidth := 2
  entry := front 0
  code := Fin.append beforeBody (fun j ↦
    ((body.code (body.labels.symm j)).map (fun t ↦ (t.map bodyLabel).getD returnPC)).emit badPC)

variable {w : ℕ}

private theorem table_front (pub : Pub → Word w) (i : Fin 7) :
    (inputTable.instantiate w pub).code (front i) = (beforeBody i).resize w := by
  simp only [Template.instantiate, inputTable, front, Fin.append_left]

theorem inputTable_linked (pub : Pub → Word w) :
    Flow.Linked (inputTable.instantiate w pub) body bodyLabel returnPC badPC := by
  constructor
  intro i
  simp only [Template.instantiate, inputTable, bodyLabel, Fin.append_right, Equiv.symm_apply_apply]

theorem inputTable_reject (pub : Pub → Word w) : (inputTable.instantiate w pub).code badPC = .reject := by
  rw [badPC, table_front]; rfl

/-- The four private ticks spent comparing the persistent cursor with the end of the two
passes. -/
def prefixEvents (w : ℕ) : List (Event w) := List.replicate 4 .tick

/-- Registers after the four entry instructions. Registers 4, 5 and 30 hold the cursor, the
rectangle size and twice that size. -/
def prefixRegs (state cells : Word w) : Regs w 48 :=
  Function.update (Function.update (Function.update (fun _ ↦ 0) (4 : Reg) state) (5 : Reg) cells)
    (30 : Reg) (cells + cells)

/-- Execute the four private prologue opcodes, preserving memory and branch choices. -/
private theorem execute_prologue (pub : Pub → Word w) (state : Word w) (m : Memory w)
    (fuel : ℕ) (bs : List Bool) :
    let M := inputTable.instantiate w pub
    execute M.program (fuel+4) (M.program.start state) m bs =
      (execute M.program fuel
        ⟨if state = pub 0 + pub 0 then front 4 else bodyLabel body.entry,
          state, prefixRegs state (pub 0), fun _ ↦ 0⟩ m bs).map (Flow.prependEvents (prefixEvents w)) := by
  let M := inputTable.instantiate w pub
  have h0 : M.code (front 0) = .stateWord 4 (front 1) := table_front pub 0
  have h1 : M.code (front 1) = .publicWord 5 0 (front 2) := table_front pub 1
  have h2 : M.code (front 2) = .binary .add 30 5 5 (front 3) := table_front pub 2
  have h3 : M.code (front 3) = .jumpEq 4 30 (front 4) (bodyLabel body.entry) := table_front pub 3
  change execute M.program (fuel+4) ⟨front 0,state,fun _ ↦ 0,fun _ ↦ 0⟩ m bs = _
  simp only [execute, Machine.program, h0, h1, h2, h3, Instr.run, Config.put, BinaryOp.eval,
    Option.map_map]
  rfl

/-- At the terminal cursor the physical RAM accepts after four private ticks. -/
theorem execute_terminal (pub : Pub → Word w) (state : Word w) (m : Memory w) (fuel : ℕ)
    (hterm : state = pub 0 + pub 0) :
    let M := inputTable.instantiate w pub
    execute M.program (fuel+5) (M.program.start state) m [] = some ⟨prefixEvents w, none⟩ := by
  dsimp only
  rw [show fuel+5 = (fuel+1)+4 by omega, execute_prologue, ite_eq_left hterm]
  have h4 : (inputTable.instantiate w pub).code (front 4) = .accept := table_front pub 4
  simp only [execute, Machine.program, h4, Instr.run, ↓reduceIte, Option.map_some]
  rfl

/-- The linked body may start with the prologue's live registers. It returns register 29
after exactly the structured trace, with the four control ticks included in the report. -/
theorem execute_data (pub : Pub → Word w) (state : Word w) (m : Memory w) (fuel : ℕ)
    (hdata : state ≠ pub 0 + pub 0) (es : List (Event w)) (final : Regs w 48) (m' : Memory w)
    (hE : Flow.Exec pub state body (prefixRegs state (pub 0)) m es final m')
    (hlen : es.length + 4 < fuel) :
    let M := inputTable.instantiate w pub
    execute M.program fuel (M.program.start state) m (choiceBits es) =
      some ⟨prefixEvents w ++ es, some (final 29)⟩ := by
  dsimp only
  let left := fuel - (es.length + 4)
  have hleft : 0 < left := Nat.sub_pos_of_lt hlen
  have he := hE.execute (inputTable_linked pub) (inputTable_reject pub) (fun _ ↦ 0) left []
  simp only [List.append_nil] at he
  have hout : (inputTable.instantiate w pub).code returnPC = .returnState 29 := table_front pub 5
  obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero hleft.ne'
  rw [ht] at he
  have hret : execute (inputTable.instantiate w pub).program (t+1)
      ⟨returnPC,state,final,fun _ ↦ 0⟩ m' [] = some ⟨[], some (final 29)⟩ := by
    simp [execute, Machine.program, hout, Instr.run]
  rw [hret, Option.map_some] at he
  rw [show fuel = (es.length+(t+1))+4 by dsimp [left] at ht; omega, execute_prologue, ite_eq_right hdata, he]
  simp [Flow.prependEvents]

end PrimedInputRAM.Opcodes

end VPVNP
end Computability
end OAI
