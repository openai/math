import OAI.Computability.BorderVNP.DiagonalNativePackedProduct
import OAI.Computability.BorderVNP.RoutingISATypedNativeValue

/-! # Live typed source rows for the positive private cell calls -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction CompactMachine CellDispatch CellMacro.Generator BorderVNP.Cube

variable {w n : ℕ}

/-- Actual source at a typed task entry. The physical packet bits and logical cell inputs
are separate, so a private routine can restore the omitted zero exterior lanes. -/
structure TypedRowsAt (gen : Fragment IO) (n : ℕ) (pub : Arg → Word w) (m : Memory w) where
  /-- First word of the seven-word compact owned-task table. -/
  table : ℕ
  /-- Number of occupied rows written for this team. -/
  count : ℕ
  /-- Native source descriptor, destination and call pointer of each owned task. -/
  tasks : ℕ → TypedBatch.Task
  /-- Logical sparse cell statement addressed by each global directory row. -/
  cells : ℕ → CellInput
  /-- Physical argument bits staged for each global directory row. -/
  payload : ℕ → List Bool
  /-- Representable live frame and exact seven-word directory fields. -/
  frame : (pub 0).val+90 < 2^w
  width : (m ((pub 0).val+30)).val=w
  base : (m ((pub 0).val+89)).val=table
  len : (m ((pub 0).val+90)).val=count
  space : table+7*count ≤ 2^w
  /-- Disjoint task and payload regions, with all live words present on the true memory. -/
  allocated : TypedBatch.Allocated w table count tasks
  stored : ∀ i < count, (tasks i).Stored m table i ∧ (tasks i).cell.Stored m
  taskRoom : ∀ i < count, (tasks i).callRow+2 < 2^w ∧ (tasks i).cell.Room w
  control : TypedBatch.ControlLayout pub m tasks count
  directory : let f := Frame.ofMemory pub m
    f.base+3*f.count ≤ 2^w
  /-- The actual compact words and their verified private execution after publication. -/
  packed : PackedRows (Frame.ofMemory pub m) (TypedBatch.written m tasks count) gen n payload
    (fun i => (cells i).stmt.expand [])

variable {gen : Fragment IO} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}

/-- Replay the final real entry to identify its exact output, and transfer the packed rows,
owners, frame, and directory extent to that output. -/
theorem TypedRowsAt.returned (rows : TypedRowsAt gen n pub m) (r : Returns TypedBatch.entry pub mac s m) :
    ∃ C : GeneratedCells gen n pub r.val.2.2, C.cell = rows.cells ∧ C.payload = rows.payload ∧
      let f := Frame.ofMemory pub r.val.2.2
      f.base+3*f.count ≤ 2^w := by
  obtain ⟨es,t,run,_,_⟩ := TypedBatch.entry_run pub mac s m rows.tasks rows.frame rows.width rows.base rows.len
    rows.space rows.allocated rows.stored rows.taskRoom
  have output := (r.property.unique_of_deterministic (by decide) run).2.2
  rw [output]
  refine ⟨⟨rows.cells,rows.payload,?_⟩,rfl,rfl,?_⟩
  · rw [rows.control.survives.1]
    exact rows.packed
  · rw [rows.control.survives.1]
    exact rows.directory

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
