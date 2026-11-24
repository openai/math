import OAI.Computability.VPVNP.PrimedInputRAMFlowEval
import OAI.Computability.VPVNP.PrimedScheduleRAM

/-!
# Finite table for a scheduled coefficient-counter call

All scheduled calls use the same structured body and reset their private
registers at entry. On success the body leaves the next cursor and the total
number of calls in two designated registers. A single comparison then either
accepts at the last item or returns the next cursor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Call

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM

variable {r k w : ℕ} (a : Flow r k)

/-- Embed a label of the scheduled call body into the finite instruction table with its four
terminal opcodes. -/
def pc (i : a.Label) : Fin (a.length + 4) := Fin.castAdd 4 (a.labels i)
/-- Continuation that compares the next cursor with the total call count after a successful
body exit. -/
def stop : Fin (a.length + 4) := ⟨a.length, by omega⟩
/-- Instruction address for a failed guard or rejected call. -/
def bad : Fin (a.length + 4) := ⟨a.length+1, by omega⟩
/-- Instruction that returns the next cursor as persistent state for the next scheduled call. -/
def back : Fin (a.length + 4) := ⟨a.length+2, by omega⟩
/-- Halting instruction reached when the next cursor equals the total number of calls. -/
def accept : Fin (a.length + 4) := ⟨a.length+3, by omega⟩

/-- Compilation introduces four terminal opcodes. Neither the input length
nor the number of calls determines the number of instruction labels. -/
def template (next total : Fin r) : Template (a.length+4) r k where
  literalWidth := 2
  entry := pc a a.entry
  code i := if hi : i.val < a.length then
      ((a.code (a.labels.symm ⟨i.val,hi⟩)).map (fun t => (t.map (pc a)).getD (stop a))).emit (bad a)
    else if i = stop a then .jumpEq next total (accept a) (back a)
    else if i = back a then .returnState next
    else if i = accept a then .accept
    else .reject

variable (next total : Fin r) (pub : Fin k → Word w)

theorem linked : Flow.Linked ((template a next total).instantiate w pub) a (pc a) (stop a) (bad a) := by
  constructor
  intro i
  simp [template, Template.instantiate, pc, (a.labels i).isLt]

theorem reject_code : ((template a next total).instantiate w pub).code (bad a) = .reject := by
  simp [Template.instantiate, template, bad, stop, back, accept, Fin.ext_iff, Instr.resize, show ¬ a.length+1 < a.length by omega]

/-- Any surplus branch bits after the last opcode reject, even if the
item itself would have succeeded on a shorter stream. -/
theorem execute_stop (state : Word w) (regs : Regs w r) (priv : Word w → Word w)
    (mem : Memory w) (bits : List Bool) (fuel : ℕ) :
    let M := (template a next total).instantiate w pub
    execute M.program (fuel+2) ⟨stop a,state,regs,priv⟩ mem bits =
      if bits.isEmpty then some ⟨[.tick], if regs next = regs total then none else some (regs next)⟩ else none := by
  let M := (template a next total).instantiate w pub
  have hs : M.code (stop a) = .jumpEq next total (accept a) (back a) := by
    simp [M, Template.instantiate, template, stop, Instr.resize]
  have ha : M.code (accept a) = .accept := by
    simp [M, Template.instantiate, template, accept, stop, back, Fin.ext_iff, Instr.resize, show ¬ a.length+3 < a.length by omega]
  have hb : M.code (back a) = .returnState next := by
    simp [M, Template.instantiate, template, back, stop, Fin.ext_iff, Instr.resize, show ¬ a.length+2 < a.length by omega]
  change execute M.program (fuel+2) _ mem bits = _
  cases bits <;> by_cases hh : regs next = regs total <;>
    simp [execute, Machine.program, hs, ha, hb, Instr.run, hh, Report.prepend]

/-- Exact native execution of a completed body, including the final cursor
comparison and halt/return and the exact-use check on the branch tape. -/
theorem execute_body (state : Word w) (regs : Regs w r) (priv : Word w → Word w)
    (mem : Memory w) {es : List (Event w)} {out : Regs w r} {mem' : Memory w}
    (hr : Flow.Exec pub state a regs mem es out mem') (extra : List Bool) (fuel : ℕ) :
    let M := (template a next total).instantiate w pub
    execute M.program (es.length + (fuel+2)) ⟨M.entry,state,regs,priv⟩ mem (choiceBits es ++ extra) =
      if extra.isEmpty then some ⟨es ++ [.tick], if out next = out total then none else some (out next)⟩ else none := by
  let M := (template a next total).instantiate w pub
  have he := hr.execute (M := M) (linked a next total pub) (reject_code a next total pub) priv (fuel+2) extra
  change execute M.program _ ⟨pc a a.entry, state, regs, priv⟩ mem _ = _
  rw [he, execute_stop a next total pub]
  cases extra <;> simp [Flow.prependEvents]

end PrimedCounter.Call

end VPVNP
end Computability
end OAI
