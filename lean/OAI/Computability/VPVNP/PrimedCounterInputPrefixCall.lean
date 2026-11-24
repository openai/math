import OAI.Computability.VPVNP.PrimedCounterInputPrefixReset
import OAI.Computability.VPVNP.PrimedCounterData
import OAI.Computability.VPVNP.PrimedCounterDispatchRun
import OAI.Computability.VPVNP.PrimedInputRAMOpcodeExecutionPrefix

/-!
# Input cells in the combined pair-counter table

Each initial cursor of the combined program invokes the two-pass input assembler
on reset registers. Dispatch contributes six private ticks and the returning
cursor comparison one more. The cut-length reads and the item itself supply all
external probes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.InputPrefix

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM Opcodes

open scoped Fin.CommRing

variable {L : Lengths} {n r H w s : ℕ} {Q : Layout L n r H w}

private theorem parser_marks (D : Data Q s) : D.parserPub (Admin.stackPublic 6) = (n : Word w) :=
  congrFun D.parserPub_stack 6

theorem assembly_lt_total (D : Data Q s) : D.assembly < D.total := by
  unfold Data.total Cursor.calls Cursor.span
  have h : 0 < (2 * 2^r) * (n + (1 + (2*n-1))) := Nat.mul_pos (by positivity) (by omega)
  omega

private theorem state_eq (i : Fin (PrimedInputRAM.positions n r + PrimedInputRAM.positions n r)) :
    cursor Q.cursorFits i.val i.isLt.le = (i.val : Word w) :=
  Fin.ext (Nat.mod_eq_of_lt (i.isLt.trans Q.cursorFits)).symm

private theorem successor_eq (i : Fin (PrimedInputRAM.positions n r + PrimedInputRAM.positions n r)) :
    successor Q.cursorFits i = PrimedSchedule.cursor w (i.val+1) :=
  Fin.ext (Nat.mod_eq_of_lt ((Nat.succ_le_of_lt i.isLt).trans_lt Q.cursorFits)).symm

/-- Compared to the standalone assembler, the enclosing dispatch contributes
two more private ticks before the body and one cursor-test tick afterwards. -/
def padded (a : Report w) : Report w :=
  ⟨(List.replicate 2 .tick ++ a.events) ++ [.tick], a.result⟩

@[simp] theorem padded_memory (a : Report w) (m : Memory w) :
    after m (padded a).events = after m a.events := by
  simp [padded, after, update]

@[simp] theorem padded_probes (a : Report w) : (padded a).probes = a.probes :=
  Dispatch.probes_framed 2 a.events

/-- Native reports agree exactly after accounting for the additional private
dispatch ticks. This includes the values of all three cut-length reads. -/
theorem cell_exec (D : Data Q s) (F : D.Fits) (i : Fin D.assembly)
    (m : Memory w) (hc : CutMemory L m) (b : Bool) :
    execute D.machine.program D.fuel (D.machine.program.start (cursor Q.cursorFits i.val i.isLt.le)) m
      ((nativeOps Q i).bits b) = some (padded ((physicalSchedule Q F.assembler).report i m b)) := by
  let st := cursor Q.cursorFits i.val i.isLt.le
  obtain ⟨cost, hcost, hh⟩ := native_body Q F.assembler i m hc (fun _ ↦ 0)
  obtain ⟨out, hr, hret⟩ := hh b
  have he := dataEvents_length m cost (nativeOps Q i) b
  have hne : st ≠ pubWord Q 0 + pubWord Q 0 := by
    have hn := pubWord_cells Q F.assembler
    have hv : ((pubWord Q 0) + (pubWord Q 0)).val = D.assembly := by
      rw [Fin.val_add_eq_of_add_lt (by rw [hn]; exact Q.cursorFits), hn]
    exact fun eq ↦ i.isLt.ne ((congrArg Fin.val eq).trans hv)
  have physical := execute_data (pubWord Q) st m (nativeFuel r) hne _ out _ (dataCall_prefixRegs hr)
    (by unfold nativeFuel; omega)
  simp only [dataEvents_choices, hret] at physical
  have report := Option.some.inj (((physicalSchedule Q F.assembler).data i m b hc).symm.trans physical)
  rw [report, state_eq (Q := Q)]
  rw [state_eq (Q := Q)] at hr
  apply (Dispatch.input_execute_iff (pubWord Q) D.parserPub (parser_marks D) F.cursor i
    (fun _ ↦ 0) (fun _ ↦ 0) m _ D.fuel _).mpr
  refine ⟨_, out, _, hr, ?_, dataEvents_choices .., rfl, ?_, ?_⟩
  · have hf : 3*r+165+20 ≤ D.fuel := le_max_left _ _
    omega
  · have hs : i.val+1 < D.total := lt_of_le_of_lt i.isLt (assembly_lt_total D)
    simp only [padded, PrimedSchedule.control, hs, ↓reduceIte, successor_eq (Q := Q)]
  · rw [padded_memory]
    change after m (dataEvents m cost (nativeOps Q i) b) = _
    exact dataEvents_memory ..

/-- Contract of the returning input calls in the genuine pair table. -/
def calls (D : Data Q s) (F : D.Fits) :
    ReturningCalls D.machine.program D.fuel (nativeOps Q) (encodeBit w) Q.cursorFits (CutMemory L) where
  report i m b := padded ((physicalSchedule Q F.assembler).report i m b)
  data i m b hc := cell_exec D F i m hc b
  result := (physicalSchedule Q F.assembler).result
  memory i m b hc := (padded_memory _ _).trans ((physicalSchedule Q F.assembler).memory i m b hc)
  closed := (physicalSchedule Q F.assembler).closed

end PrimedCounter.InputPrefix

end VPVNP
end Computability
end OAI
