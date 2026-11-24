import OAI.Computability.VPVNP.CompressorRecordsSchedule
import OAI.Computability.VPVNP.LiveHeaderProtectedCore

/-!
# Gathering the two demand widths of a shrinking motif

Each visit copies a pair of words from two strided source arrays into adjacent
cells of the demand array. The cursor enumerates rows and columns in row-major
order. The visit reads both widths before writing the pair, so its memory
formula holds even when source and destination addresses coincide.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkDemandGather

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- Parameter zero is the number of visited columns in a row. Parameters one
and two are the source row strides, three and four the source bases, and five
the output base. Registers five and six retain the two widths until the writes. -/
def ops : List (Op 7 6) :=
  [.stateWord 0, .publicWord 1 0, .binary .div 2 0 1, .binary .mod 3 0 1,
   .publicWord 1 1, .binary .mul 4 2 1, .publicWord 1 3,
   .binary .add 4 1 4, .binary .add 4 4 3, .read 5 4,
   .publicWord 1 2, .binary .mul 4 2 1, .publicWord 1 4,
   .binary .add 4 1 4, .binary .add 4 4 3, .read 6 4,
   .publicWord 1 5, .binary .add 1 1 0, .binary .add 1 1 0, .write 1 5,
   .constant 4 1, .binary .add 1 1 4, .write 1 6, .binary .add 0 0 4]

/-- The scheduled worker that copies a motif's two demand widths into adjacent words and
returns the next motif cursor. -/
def pass : Schedule.Pass := ⟨_, _, _, template ops 0⟩

/-- Instantiate the demand-gather worker with the six words giving its column count, source
strides and bases, and dense output base. -/
def program (p : Fin 6 → Word w) := (pass.table.instantiate w p).program

/-- Decode cursor `i` into a row and column and compute the source address using the specified
stride and base operands. -/
def src (p : Fin 6 → Word w) (i : Word w) (stride base : Fin 6) : Word w :=
  p base + BinaryOp.div.eval i (p 0) * p stride + BinaryOp.mod.eval i (p 0)

/-- Address of the first of the two dense demand words for cursor `i`, two words per motif from
the output base. -/
def dst (p : Fin 6 → Word w) (i : Word w) : Word w := p 5 + i + i

/-- Number of native operations for one demand-width pair, including the two reads, two writes
and cursor increment. -/
def cost : ℕ := ops.length

theorem cost_eq : cost = 24 := rfl

/-- Complete report of a call, with each read carrying the word from the
incoming memory. The returned cursor points to the next width pair. -/
def visits (p : Fin 6 → Word w) (i : Word w) (m : Memory w) : Report w :=
  let a := src p i 1 3
  let b := src p i 2 4
  let d := dst p i
  ⟨List.replicate 9 .tick ++ [.read a (m a.val)] ++
    List.replicate 5 .tick ++ [.read b (m b.val)] ++
    [.tick, .tick, .tick, .write d (m a.val), .tick, .tick, .write (d+1) (m b.val), .tick],
   some (i+1)⟩

theorem visits_result (p : Fin 6 → Word w) (i : Word w) (m : Memory w) :
    (visits p i m).result = some (i+1) := rfl

theorem visit_cost (p : Fin 6 → Word w) (i : Word w) (m : Memory w) :
    (visits p i m).events.length = cost ∧ countProbes (visits p i m).events = 4 ∧
      choiceBits (visits p i m).events = [] := ⟨rfl, rfl, rfl⟩

theorem visit_ticks (p : Fin 6 → Word w) (i : Word w) (m : Memory w) :
    (visits p i m).events.count .tick = 20 := rfl

theorem visit_after (p : Fin 6 → Word w) (i : Word w) (m : Memory w) :
    after m (visits p i m).events =
      writeMemory (writeMemory m (dst p i) (m (src p i 1 3).val))
        (dst p i+1) (m (src p i 2 4).val) := rfl

private theorem visit_trace (p : Fin 6 → Word w) (i : Word w) (m : Memory w) :
    ∃ rs m', trace p i ops (fun _ ↦ 0) m = some ((visits p i m).events, rs, m') ∧
      rs 0 = i+1 := by
  simp (config := { decide := true }) [ops, trace, visits, src, dst, Op.effect,
    Function.update, BinaryOp.eval, List.replicate_succ]
  rfl

/-- Every cap allowing the 24 instructions and their return produces the stated
report at the normal entry point of the scheduler's finite worker table. -/
theorem visit_run (p : Fin 6 → Word w) (i : Word w) (m : Memory w) {cap : ℕ}
    (hcap : cost < cap) :
    execute (program p) cap ((program p).start i) m [] = some (visits p i m) := by
  have run : execute (program p) (1 + cost) ((program p).start i) m [] = some (visits p i m) := by
    obtain ⟨rs, m', ht, hr⟩ := visit_trace p i m
    let M := (template ops 0).instantiate w p
    change execute M.program (1 + ops.length) ⟨M.entry, i, fun _ ↦ 0, fun _ ↦ 0⟩ m [] = _
    rw [execute_template, run_eq_trace, ht]
    simp [hr, visits]
  have h := execute_extend run (cap - (1 + cost))
  simpa only [show 1 + cost + (cap - (1 + cost)) = cap by omega] using h

end CompressorRecords.ShrinkDemandGather

end VPVNP
end Computability
end OAI
