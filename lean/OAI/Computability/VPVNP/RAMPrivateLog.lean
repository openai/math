import OAI.Computability.VPVNP.RAMProgram

/-!
# Linear-scan private memory

A fresh call has an empty list of writes. Storing a word conses an address and
value, while loading scans from the head and defaults to zero. A write to a
previously used address therefore supersedes its older entries. Each scan
compares full words without ever iterating up to a supplied address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C D : Type*}

/-- Change only the private continuations of an instruction, including both
binary continuations and every possible read answer. -/
def CallAction.mapState (f : C → D) : CallAction w C → CallAction w D
  | .localStep c => .localStep (f c)
  | .branch g => .branch (fun b => f (g b))
  | .read a g => .read a (fun v => f (g v))
  | .write a v c => .write a v (f c)
  | .finish r => .finish r
  | .reject => .reject

namespace PrivateRAM

variable {p r k : ℕ}

/-- A newest-first list of private address-value writes. Looking up the first matching address
recovers its latest word. -/
abbrev WriteLog (w : ℕ) := List (Word w × Word w)

/-- A scan returns the newest value and a charge for testing the list, reading
the address, comparing it, and either advancing or copying the value. -/
def WriteLog.scan : WriteLog w → Word w → Word w × ℕ
  | [], _ => (0, 1)
  | (key, v) :: rest, a =>
    if a = key then (v, 4)
    else let t := scan rest a; (t.1, 4 + t.2)

theorem WriteLog.scan_work_le (log : WriteLog w) (a : Word w) :
    (WriteLog.scan log a).2 ≤ 4 * (log.length + 1) := by
  induction log with
  | nil => simp [WriteLog.scan]
  | cons e log ih =>
    obtain ⟨key, v⟩ := e
    by_cases h : a = key <;> simp [WriteLog.scan, h] <;> omega

/-- The total memory function represented by the log. -/
def WriteLog.memory (log : WriteLog w) (a : Word w) : Word w := (WriteLog.scan log a).1

@[simp] theorem WriteLog.memory_nil : WriteLog.memory ([] : WriteLog w) = fun _ => 0 := rfl

theorem WriteLog.memory_cons (log : WriteLog w) (key v : Word w) :
    WriteLog.memory ((key, v) :: log) = Function.update (WriteLog.memory log) key v := by
  funext a
  by_cases h : a = key <;> simp [WriteLog.memory, WriteLog.scan, h, Function.update_of_ne]

/-- Private RAM configuration with its program counter, persistent word, registers and a
newest-first log of writes. -/
structure LogConfig (w p r : ℕ) where
  /-- Instruction address currently selected in the private machine's finite program table. -/
  pc : Fin p
  /-- Persistent word carried in the current private call configuration. -/
  persistent : Word w
  /-- Current contents of the private word registers. -/
  reg : Fin r → Word w
  /-- Newest-first list of private stores since the beginning of the call. -/
  writes : WriteLog w

/-- Interpret a logged configuration as an ordinary RAM configuration by evaluating its write
log as a private memory. -/
def LogConfig.denote (l : LogConfig w p r) : Config w p r :=
  ⟨l.pc, l.persistent, l.reg, WriteLog.memory l.writes⟩

/-- A store extends the log once. Every other opcode retains the current log. -/
def Instr.nextLog (i : Instr w p r k) (l : LogConfig w p r) : WriteLog w :=
  match i with
  | .storePrivate addr src _ => (l.reg addr, l.reg src) :: l.writes
  | _ => l.writes

theorem Instr.nextLog_length_le (i : Instr w p r k) (l : LogConfig w p r) :
    (i.nextLog l).length ≤ l.writes.length + 1 := by cases i <;> simp [Instr.nextLog]

/-- Use the instruction's register and control updates unchanged. In the
input configuration the private read operation is the linear scan, and in
every continuing output the writes are kept as a list. -/
def Instr.runLogged (i : Instr w p r k) (pub : Fin k → Word w) (l : LogConfig w p r) :
    CallAction w (LogConfig w p r) :=
  (i.run pub l.denote).mapState fun c => ⟨c.pc, c.persistent, c.reg, i.nextLog l⟩

/-- The logged dispatcher implements all of the direct-memory opcodes. -/
theorem Instr.runLogged_correct (i : Instr w p r k) (pub : Fin k → Word w) (l : LogConfig w p r) :
    (i.runLogged pub l).mapState LogConfig.denote = i.run pub l.denote := by
  cases i <;>
    simp [Instr.runLogged, Instr.run, CallAction.mapState, Instr.nextLog, LogConfig.denote,
      Config.put, Config.store, WriteLog.memory_cons]

/-- Resetting the private log is independent of the width of the address
space. Public data and the persistent state have the native interpretation. -/
def Machine.logProgram (M : Machine w p r k) : Program w (LogConfig w p r) where
  start s := ⟨M.entry, s, fun _ => 0, []⟩
  step l := (M.code l.pc).runLogged M.publicData l

theorem Machine.logProgram_start (M : Machine w p r k) (s : Word w) :
    (M.logProgram.start s).denote = M.program.start s := rfl

theorem Machine.logProgram_step (M : Machine w p r k) (l : LogConfig w p r) :
    (M.logProgram.step l).mapState LogConfig.denote = M.program.step l.denote :=
  (M.code l.pc).runLogged_correct M.publicData l

end PrivateRAM
end BurstRAM

end VPVNP
end Computability
end OAI
