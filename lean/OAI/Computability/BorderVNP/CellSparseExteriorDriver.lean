import OAI.Computability.BorderVNP.CellSparseExteriorRestore
import OAI.Computability.BorderVNP.RoutingISATypedPrivateClock

/-! # Actual private path sum for an RLE cell burst on the original dense logical bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open VPVNP.BurstRAM CellMacro CellMacro.Generator CellSparse CompactMachine CellDispatch

/-- The true, relatively addressed external slices of one prepared cell. -/
structure Field where
  /-- Number of supplied logical wire bits before the reports. -/
  width : ℕ
  /-- Ordered occupied intervals of that logical bank. -/
  spans : List Span
  /-- Raw reported counts and any source-use bits. -/
  tail : List Bool

/-- Bytes actually staged and fetched at the shared external interface. -/
def Field.bytes (e : Field) := encode e.width e.tail 0 e.spans

/-- The logical values presented to all original sparse directory operations. -/
def Field.values (e : Field) := expand e.width e.tail 0 e.spans

/-- The complete fixed private machine first restores the dense external slots, then
invokes the actual typed compiler, sparse generator and signed bytecode. -/
noncomputable def driver := CompactPacket.driver (Private.restore.seq CellPrivate.translate) 8 3

/-- The private work spent on restoring and reversing the logical bank. -/
def Field.restoreCost (e : Field) := Private.cost e.width e.tail 0 e.spans+2*e.values.length+1

/-- All true private work plus the actual sized burst reads. -/
noncomputable def clock (w : ℕ) (D : Directory) (k : ℕ) (e : Field) :=
  let payload := Packet.input D k e.bytes
  let ops := (withExternal e.values (D.program k)).expand []
  2*(3*((CompactFrame.pack w payload).length*w) +
    CompactPacket.generationCost 8 (Packet.bits D k) e.values (D.program k) (e.restoreCost+CellPrivate.translateClock D k) +
    (2*(stream ops).length+1)+budget ops)

/-- Real execution on the sparse supplied payload returns the original logical
external directory's code, including its signed terms and all private choices. -/
theorem driver_run (D : Directory) (k : ℕ) (e : Field) (widths : D.ProfileWidths) :
    ∃ t ≤ CompactPacket.generationCost 8 (Packet.bits D k) e.values (D.program k)
        (e.restoreCost+CellPrivate.translateClock D k),
      driver.Runs t (io (Packet.input D k e.bytes) [] [])
        (io [] [] (stream ((withExternal e.values (D.program k)).expand [])).reverse) := by
  obtain ⟨s,hs,restore⟩ := Private.restore_run e.width 0 e.tail e.spans (Packet.bits D k) []
  obtain ⟨t,ht,translated⟩ := CellPrivate.translate_run D k e.values widths
  have full := Fragment.runs_seq _ _ restore translated
  obtain ⟨u,hu,run⟩ := CompactPacket.driver_run_external (Private.restore.seq CellPrivate.translate) 8 3
    (Packet.bits D k) e.bytes e.values (D.program k) (D.program_fitsDepth _) full
  change s ≤ e.restoreCost at hs
  refine ⟨u,?_,run⟩
  dsimp only [CompactPacket.generationCost] at hu ⊢
  omega

/-- The signed sum on the actual fetched burst is the true directory value on the
zero-restored external assignment. -/
theorem cell_value {w n : ℕ} (D : Directory) (k : ℕ) (e : Field) (hw : 0<w) (widths : D.ProfileWidths)
    (room : clock w D k e ≤ n^25) :
    ∑ o ∈ choices driver n (CompactFrame.pack w (Packet.input D k e.bytes)), o.2.value =
      ∑ x : Fin k → Bool, D.weight (lookup (List.ofFn x++e.values)) := by
  obtain ⟨t,ht,run⟩ := driver_run D k e widths
  apply Eq.trans (sum_choices_packed driver n hw (Packet.input D k e.bytes) _ run ?_)
    (value_external_directory ..)
  dsimp only [clock] at room
  omega

/-- Physical packed-row certification for the prepared RLE driver and the logical
cells consumed by the signed continuation. The actual seven-word task postimage
supplies the compact bytes, while each bytecode reads the restored logical values. -/
theorem packedRows {w table count n : ℕ} {pub : Arg → Word w} {m : Memory w}
    {tasks : ℕ → TypedBatch.Task} (D : ℕ → Directory) (k : ℕ → ℕ) (ext : ℕ → Field) (hw : 0 < w)
    (placed : TypedBatch.PlacedRows pub m tasks count n (fun i => ⟨D i,k i,(ext i).bytes⟩))
    (layout : TypedBatch.Allocated w table count tasks) (room : ∀ j < count, (tasks j).cell.Room w)
    (control : TypedBatch.ControlLayout pub m tasks count)
    (data : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val=(Frame.ofMemory pub m).team →
      (D i).ProfileWidths ∧ clock w (D i) (k i) (ext i) ≤ n^25) :
    PackedRows (Frame.ofMemory pub m) (TypedBatch.written m tasks count) driver n
      (fun i => Packet.input (D i) (k i) (ext i).bytes)
      (fun i => (withExternal (ext i).values ((D i).program (k i))).expand []) := by
  have args := placed.arguments layout room control
  refine ⟨hw,fun i hi ho => (args i hi ho).1,fun i hi ho => (args i hi ho).2.1,
    fun i hi ho => (args i hi ho).2.2,?_⟩
  intro i hi ho
  obtain ⟨widths,bound⟩ := data i hi (by rw [←control.survives.2 i hi]; exact ho)
  obtain ⟨t,ht,run⟩ := driver_run (D i) (k i) (ext i) widths
  refine ⟨t,run,?_⟩
  dsimp only [clock] at bound
  omega

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
