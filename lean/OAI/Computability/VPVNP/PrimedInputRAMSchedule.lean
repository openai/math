import OAI.Computability.VPVNP.PrimedInputRAMCopy
import OAI.Computability.VPVNP.RAMChain

/-!
# A cursor-controlled burst RAM for the two primed input passes

Each public cursor dispatches one skip, choice-and-write, literal write, or read-and-write.
Private control is re-created at the beginning of each call. The external memory is read
only by a `read` instruction. Cursor `M` is an explicit halt, so the `M` data calls can
also be used as a prefix returning the terminal cursor for the subsequent grammar parse.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM

variable {M w : ℕ}

/-- One input-pass action. It skips a position, stores a chosen bit at an address, or copies a
literal or fetched word to its destination. -/
inductive Item (w : ℕ)
  | skip
  | choose (addr : Word w)
  | copy (src : CopySource w) (dest : Word w)

/-- Test whether this schedule item consumes a nondeterministic bit choice. -/
def Item.owns : Item w → Bool
  | .choose _ => true
  | _ => false

/-- The exact choice stream for one item, a singleton for a choice and empty for a skip or
copy. -/
def Item.bits (op : Item w) (b : Bool) : List Bool := if op.owns then [b] else []

/-- Events and successor cursor for the scheduled action on the supplied memory and choice bit. -/
def Item.report (op : Item w) (bitWord : Bool → Word w) (next : Word w) (m : Memory w)
    (b : Bool) : Report w :=
  match op with
  | .skip => ⟨[], some next⟩
  | .choose a => cellReport true a next bitWord b
  | .copy src dst => copyReport src dst next m

/-- External memory after a skip, a write of an encoded choice bit, or a copy from the
indicated source. -/
def Item.memory (op : Item w) (bitWord : Bool → Word w) (m : Memory w) (b : Bool) : Memory w :=
  match op with
  | .skip => m
  | .choose a => writeMemory m a (bitWord b)
  | .copy src dst => writeMemory m dst (CopySource.get m src)

@[simp] theorem Item.report_result (op : Item w) (bitWord : Bool → Word w) (next : Word w)
    (m : Memory w) (b : Bool) : (op.report bitWord next m b).result = some next := by
  cases op <;> rfl

@[simp] theorem Item.after_report (op : Item w) (bitWord : Bool → Word w) (next : Word w)
    (m : Memory w) (b : Bool) : after m (op.report bitWord next m b).events = op.memory bitWord m b := by
  cases op with
  | skip | choose => rfl
  | copy src dst => exact after_copyReport src dst next m

theorem Item.report_probes (op : Item w) (bitWord : Bool → Word w) (next : Word w)
    (m : Memory w) (b : Bool) : (op.report bitWord next m b).probes ≤ 2 := by
  cases op with
  | skip | choose => simp [Item.report, Report.probes, cellReport, countProbes]
  | copy src dst => cases src <;> simp [Item.report, Report.probes, copyReport, countProbes]

/-- Represent a schedule position up to and including the terminal position as a word, using
the bound on the entire schedule. -/
def cursor (fit : M < 2^w) (k : ℕ) (hk : k ≤ M) : Word w := ⟨k, hk.trans_lt fit⟩

/-- Cursor returned after executing the item at index `i`, representing position `i + 1`. -/
def successor (fit : M < 2^w) (i : Fin M) : Word w := cursor fit (i.val+1) i.isLt

/-- Control states of the scheduled input machine for visiting an item, writing its word,
returning the next cursor, halting or rejecting an invalid cursor. -/
inductive Dispatch (w : ℕ)
  | visit (op : Item w) (next : Word w)
  | write (addr value next : Word w)
  | finish (next : Word w)
  | halt
  | invalid

/-- Execute one schedule item per burst call, branch at each bit choice, and halt when the
persistent cursor reaches the item count. -/
def scheduledProgram (ops : Fin M → Item w) (bitWord : Bool → Word w) (fit : M < 2^w) :
    Program w (Dispatch w) where
  start s := if h : s.val < M then .visit (ops ⟨s.val, h⟩) (successor fit ⟨s.val,h⟩)
    else if s.val = M then .halt else .invalid
  step
    | .visit .skip next => .finish (some next)
    | .visit (.choose a) next => .branch (fun b ↦ .write a (bitWord b) next)
    | .visit (.copy (.literal v) dst) next => .write dst v (.finish next)
    | .visit (.copy (.fetch a) dst) next => .read a (fun v ↦ .write dst v next)
    | .write a v next => .write a v (.finish next)
    | .finish next => .finish (some next)
    | .halt => .finish none
    | .invalid => .reject

/-- Terminal schedule report with an empty trace and no successor cursor. -/
def haltReport (w : ℕ) : Report w := ⟨[], none⟩

/-- Reports of a schedule on the designated branch bits, evaluating each fetch against
memory after the preceding call. The final halt is separate. -/
def scheduledReports (ops : Fin M → Item w) (bitWord : Bool → Word w) (fit : M < 2^w)
    (f : Fin M → Bool) : List (Fin M) → Memory w → List (Report w)
  | [], _ => []
  | i :: xs, m => (ops i).report bitWord (successor fit i) m (f i) ::
    scheduledReports ops bitWord fit f xs ((ops i).memory bitWord m (f i))

@[simp] theorem start_item (ops : Fin M → Item w) (bitWord : Bool → Word w) (fit : M < 2^w)
    (i : Fin M) : (scheduledProgram ops bitWord fit).start (cursor fit i.val i.isLt.le) =
      .visit (ops i) (successor fit i) := by simp [scheduledProgram, cursor, i.isLt]

@[simp] theorem start_halt (ops : Fin M → Item w) (bitWord : Bool → Word w) (fit : M < 2^w) :
    (scheduledProgram ops bitWord fit).start (cursor fit M le_rfl) = .halt := by
  simp [scheduledProgram, cursor]

theorem execute_item (ops : Fin M → Item w) (bitWord : Bool → Word w) (fit : M < 2^w)
    (op : Item w) (next : Word w) (m : Memory w) (b : Bool) :
    execute (scheduledProgram ops bitWord fit) 3 (.visit op next) m (op.bits b) =
      some (op.report bitWord next m b) := by
  cases op with
  | skip | choose => rfl
  | copy src dst => cases src <;> rfl

/-- A successful data call consumes one bit precisely at a choice instruction. -/
theorem execute_item_only (ops : Fin M → Item w) (bitWord : Bool → Word w) (fit : M < 2^w)
    (op : Item w) (next : Word w) (m : Memory w) (bs : List Bool) (r : Report w)
    (h : execute (scheduledProgram ops bitWord fit) 3 (.visit op next) m bs = some r) :
    ∃ b, bs = op.bits b ∧ r = op.report bitWord next m b := by
  cases op with
  | skip =>
    cases bs with
    | nil => exact ⟨false, rfl, (Option.some.inj h).symm⟩
    | cons => contradiction
  | choose a =>
    cases bs with
    | nil => contradiction
    | cons b bs => cases bs with
      | nil => exact ⟨b, rfl, (Option.some.inj h).symm⟩
      | cons => contradiction
  | copy src dst =>
    cases bs with
    | nil => cases src <;> exact ⟨false, rfl, (Option.some.inj h).symm⟩
    | cons => cases src <;> contradiction

end PrimedInputRAM

end VPVNP
end Computability
end OAI
