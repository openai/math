import OAI.Hierarchy.TraceReceiverTaskShape
import OAI.Hierarchy.TraceReceiverPreparation

namespace OAI
/-! # Exact hardware count for the five-word terminal task preparation -/

namespace Hierarchy.TraceReceiverTasks

open ThreeFlat RAM DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure

open private headerBinds widthBinds prefixWork header_binds width_binds prefix_work
  from OAI.Hierarchy.TraceReceiverPreparation

private def rowBinds : ℕ :=
  (row (W := 1) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩).binds

private theorem row_binds (W : ℕ) (D : Layout) : (row (W := W) D).binds = rowBinds := by
  simp only [rowBinds, row, Term.select, Term.binary, Term.load, Term.literal, Term.binds_letThen,
    Term.binds_rename, Term.binds]

private def rangeHardware : ℕ := 11 + 4 * headerBinds

private def columnHardware : ℕ :=
  rangeHardware + (18 + 4 * widthBinds) + (18 + 4 * prefixWork)

/-- Three width and prefix columns, followed by a header write and the terminal task scan. -/
def beforeHardware : ℕ := 3 * columnHardware + rangeHardware + (18 + 4 * rowBinds)

private theorem range_size (W head count width dst mul : ℕ) :
    size (rangeSeed W head count width dst mul) = rangeHardware := by
  simp only [rangeSeed, size_writing, header_binds, rangeHardware, Nat.add_zero]

private theorem column_size (W head count selected first results width dest cap : ℕ) (j : Fin 3) :
    size (column W head count selected first results width dest cap j) = columnHardware := by
  simp only [column, size_seq, range_size, amountScan, size_scan,
    width_binds, HeaderScan.binds_closed, prefix_work, columnHardware]

theorem before_size (W : ℕ) (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) :
    size (before W D count cap width) = beforeHardware := by
  simp only [before, size_seq, column_size, range_size, procedure, size_scan, row_binds,
    beforeHardware, Nat.succ_mul, Nat.zero_mul, Nat.zero_add]


end Hierarchy.TraceReceiverTasks

end OAI
