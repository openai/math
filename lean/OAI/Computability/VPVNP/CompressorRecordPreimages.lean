import OAI.Computability.VPVNP.CompressorRecordTable
import OAI.Computability.VPVNP.RAMChain

/-!
# Scanning the placement array into local preimage lists

In the third scan of Appendix E, the selected layout has assigned each old site to one
new owner. Visit the old sites in index order. One fixed RAM call reads the selected
owner, appends the old site's index to that owner's bounded list, and returns the next
old index in the persistent state. The call rejects a malformed owner or an exhausted
row. The local traversal of §13 then has all immediate preimages in directly addressed
order, even when the same old vertex supplied several distinct motif roles.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

/-- Public words give the old-site count, owner-array base, new-site count, count-array
base, row width, and row-array base. Register 3 is the old-site index. -/
def prepareRow : List (Op 7 6) :=
  [.stateWord 3, .publicWord 4 0, .guardLt 3 4, .publicWord 4 1,
    .binary .add 4 4 3, .read 5 4, .publicWord 4 2, .guardLt 5 4,
    .publicWord 0 3, .binary .add 0 0 5, .publicWord 2 4,
    .binary .mul 5 5 2, .publicWord 1 5, .binary .add 1 1 5]

/-- One call per old index. Register 6 is the unit loaded by the append operation. -/
def collectPreimage : List (Op 7 6) :=
  prepareRow ++ appendRecord ++ [.binary .add 3 3 6]

variable {w : ℕ}

/-- Read the selected new owner of an old site from the placement array. -/
def ownerAt (pub : Fin 6 → Word w) (mem : Memory w) (i : Word w) : Word w :=
  mem (pub 1 + i).val

/-- Address of the current preimage count for one new owner. -/
def countAt (pub : Fin 6 → Word w) (owner : Word w) : Word w := pub 3 + owner

/-- First address of an owner's preimage list, using the public row capacity as its stride. -/
def rowAt (pub : Fin 6 → Word w) (owner : Word w) : Word w := pub 5 + owner * pub 4

/-- Exact physical update of the count and data cells by this one scan call. -/
def collectUpdate (pub : Fin 6 → Word w) (mem : Memory w) (i : Word w) : Memory w :=
  let owner := ownerAt pub mem i
  let c := countAt pub owner
  let length := mem c.val
  writeMemory (writeMemory mem (rowAt pub owner + length) i) c (length + 1)

/-- The report of a successful visit includes the two reads and two writes. -/
def collectEvents (pub : Fin 6 → Word w) (mem : Memory w) (i : Word w) : List (Event w) :=
  let owner := ownerAt pub mem i
  let c := countAt pub owner
  let length := mem c.val
  [.tick, .tick, .tick, .tick, .tick, .read (pub 1 + i) owner, .tick, .tick,
    .tick, .tick, .tick, .tick, .tick, .tick, .read c length, .tick, .tick,
    .write (rowAt pub owner + length) i, .tick, .tick, .write c (length + 1), .tick]

theorem collectPreimage_trace (pub : Fin 6 → Word w) (i : Word w) (regs : Regs w 7)
    (mem : Memory w) (hi : i < pub 0) (ho : ownerAt pub mem i < pub 2)
    (hcap : mem (countAt pub (ownerAt pub mem i)).val < pub 4) :
    ∃ rs, trace pub i collectPreimage regs mem =
      some (collectEvents pub mem i, rs, collectUpdate pub mem i) ∧ rs 3 = i + 1 := by
  unfold ownerAt countAt at *
  simp (config := { decide := true }) [collectPreimage, prepareRow, appendRecord, trace,
    Op.effect, BinaryOp.eval, Function.update, hi, ho, hcap, collectEvents, collectUpdate,
    ownerAt, countAt, rowAt]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem collectPreimage_invalid (pub : Fin 6 → Word w) (i : Word w) (regs : Regs w 7)
    (mem : Memory w) (h : ¬(i < pub 0 ∧ ownerAt pub mem i < pub 2 ∧
      mem (countAt pub (ownerAt pub mem i)).val < pub 4)) :
    trace pub i collectPreimage regs mem = none := by
  unfold ownerAt countAt at h
  by_cases hi : i < pub 0 <;>
    by_cases ho : mem (pub 1 + i).val < pub 2 <;>
    simp (config := { decide := true }) [collectPreimage, prepareRow, appendRecord, trace,
      Op.effect, BinaryOp.eval, Function.update, hi, ho] at h ⊢
  simp [not_lt_of_ge h]

/-- The physical write log implements precisely the two updates used in the next call. -/
theorem after_collectEvents (pub : Fin 6 → Word w) (mem : Memory w) (i : Word w) :
    after mem (collectEvents pub mem i) = collectUpdate pub mem i := rfl

theorem collectEvents_work (pub : Fin 6 → Word w) (mem : Memory w) (i : Word w) :
    (collectEvents pub mem i).length = 22 ∧ countProbes (collectEvents pub mem i) = 4 := by
  exact ⟨rfl, rfl⟩

/-- A scan visit through the fixed native table, starting with zeroed private state. -/
theorem collectPreimage_native (pub : Fin 6 → Word w) (mem : Memory w) (i : Word w)
    (hi : i < pub 0) (ho : ownerAt pub mem i < pub 2)
    (hcap : mem (countAt pub (ownerAt pub mem i)).val < pub 4) :
    let M := (template collectPreimage 3).instantiate w pub
    execute M.program 23 (M.program.start i) mem [] =
      some ⟨collectEvents pub mem i, some (i + 1)⟩ := by
  obtain ⟨rs, ht, hrs⟩ := collectPreimage_trace pub i (fun _ => 0) mem hi ho hcap
  let M := (template collectPreimage 3).instantiate w pub
  change execute M.program (1 + collectPreimage.length) ⟨M.entry, i, fun _ => 0, fun _ => 0⟩ mem [] = _
  rw [execute_template, run_eq_trace, ht]
  simp [hrs]

end CompressorRecords

end VPVNP
end Computability
end OAI
