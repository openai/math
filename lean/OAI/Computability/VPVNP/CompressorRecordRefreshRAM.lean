import OAI.Computability.VPVNP.CompressorRecordTable

/-!
# Writing external segment records during a degree refresh

Appendix E visits the source ports of each bundle consecutively. The directory stores the
translated destination bundle and the port displacement for each source bundle. Each visit
reads the old width and the running total. It writes the offset at both ends, the incoming
width at the translated port, and the new total. The outgoing width remains directly
available in the old-width array. All addresses below are word addresses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RefreshRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- Public words, in order, are the degree, old widths, bundle targets, port shifts,
bundle totals, outgoing offsets, incoming offsets and incoming widths. The persistent
state is the source segment number in bundle-major order. -/
def visit : List (Op 12 8) :=
  [.stateWord 0, .publicWord 1 0, .binary .div 2 0 1, .binary .mod 3 0 1,
    .publicWord 4 2, .binary .add 4 4 2, .read 5 4,
    .publicWord 4 3, .binary .add 4 4 2, .read 6 4,
    .binary .bitXor 6 3 6, .binary .mul 5 5 1, .binary .add 5 5 6,
    .publicWord 4 1, .binary .add 4 4 0, .read 7 4,
    .publicWord 8 4, .binary .add 8 8 2, .read 9 8,
    .publicWord 4 5, .binary .add 4 4 0, .write 4 9,
    .publicWord 4 6, .binary .add 4 4 5, .write 4 9,
    .publicWord 4 7, .binary .add 4 4 5, .write 4 7,
    .binary .add 9 9 7, .write 8 9, .constant 10 1, .binary .add 0 0 10]

/-- Recover the source bundle from a segment ordinal by dividing by the port count. -/
def bundle (p : Fin 8 → Word w) (i : Word w) : Word w := BinaryOp.div.eval i (p 0)

/-- Find the incoming segment ordinal using the stored target bundle and the source port
translated by the bundle's XOR shift. -/
def destination (p : Fin 8 → Word w) (m : Memory w) (i : Word w) : Word w :=
  let b := bundle p i
  let j := BinaryOp.mod.eval i (p 0)
  let t := m (p 2 + b).val
  let shift := m (p 3 + b).val
  t * p 0 + BinaryOp.bitXor.eval j shift

/-- Physical update, including the two offset records in the same source-port order. -/
def update (p : Fin 8 → Word w) (m : Memory w) (i : Word w) : Memory w :=
  let b := bundle p i
  let j := destination p m i
  let width := m (p 1 + i).val
  let offset := m (p 4 + b).val
  let out := writeMemory m (p 5 + i) offset
  let inc := writeMemory (writeMemory out (p 6 + j) offset) (p 7 + j) width
  writeMemory inc (p 4 + b) (offset + width)

/-- External accesses and local word steps in scan order. -/
def events (p : Fin 8 → Word w) (m : Memory w) (i : Word w) : List (Event w) :=
  let b := bundle p i
  let j := destination p m i
  let width := m (p 1 + i).val
  let offset := m (p 4 + b).val
  [.tick, .tick, .tick, .tick, .tick, .tick, .read (p 2 + b) (m (p 2 + b).val),
    .tick, .tick, .read (p 3 + b) (m (p 3 + b).val), .tick, .tick, .tick,
    .tick, .tick, .read (p 1 + i) width, .tick, .tick, .read (p 4 + b) offset,
    .tick, .tick, .write (p 5 + i) offset, .tick, .tick, .write (p 6 + j) offset,
    .tick, .tick, .write (p 7 + j) width, .tick, .write (p 4 + b) (offset + width), .tick, .tick]

theorem events_work (p : Fin 8 → Word w) (m : Memory w) (i : Word w) :
    (events p m i).length = 32 ∧ countProbes (events p m i) = 8 := ⟨rfl, rfl⟩

theorem events_after (p : Fin 8 → Word w) (m : Memory w) (i : Word w) :
    after m (events p m i) = update p m i := rfl

set_option maxRecDepth 4096 in
private theorem visit_trace (p : Fin 8 → Word w) (m : Memory w) (i : Word w) (r : Regs w 12) :
    ∃ rs, trace p i visit r m = some (events p m i, rs, update p m i) ∧ rs 0 = i + 1 := by
  simp (config := {decide := true}) [visit, events, update, bundle, destination, trace, Op.effect,
    BinaryOp.eval, Function.update]
  rfl

/-- From zeroed call-local memory the fixed table returns the next source identifier.
Its eight probes cover both ends even for a zero-width wire. -/
theorem visit_native (p : Fin 8 → Word w) (m : Memory w) (i : Word w) :
    let M := (template visit 0).instantiate w p
    execute M.program 33 (M.program.start i) m [] = some ⟨events p m i, some (i + 1)⟩ := by
  obtain ⟨rs, ht, hr⟩ := visit_trace p m i (fun _ => 0)
  let M := (template visit 0).instantiate w p
  change execute M.program (1 + visit.length) ⟨M.entry, i, fun _ => 0, fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace, ht]
  simp [hr]

/-- The updated total is the exact right endpoint whenever the bundle fits in one word. -/
theorem prefix_exact (x y : Word w) (h : x.val + y.val < 2 ^ w) :
    (x + y).val = x.val + y.val := by rw [Fin.val_add, Nat.mod_eq_of_lt h]

end CompressorRecords.RefreshRAM

end VPVNP
end Computability
end OAI
