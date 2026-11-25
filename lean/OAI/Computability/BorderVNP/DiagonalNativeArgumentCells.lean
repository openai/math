import OAI.Computability.BorderVNP.DiagonalNativeArgumentRoster
import OAI.Computability.BorderVNP.DiagonalNativeOwnedCellInputs
import OAI.Computability.BorderVNP.DiagonalNativeSparseContinuation
import OAI.Computability.BorderVNP.DiagonalNativeTypedContinuation

/-! # Logical cells and compressed payloads on every true signed argument return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellDispatch TypedTaskBuilder CellPacket.Supplement.Batch CompactMachine CellSparse

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}

/-- On the actual native producer prefix, the sparse source's compressed memory
is precisely the last input to the typed serializer. The preceding actual row emitter,
bucket, task producer and both argument writers supply the chronology. -/
theorem beforeTyped_memory (x : Returns SignedPrep.arguments pub mac s m)
    (before : Returns SignedPrep.beforeTyped pub mac s m) :
    let parts := (argumentVisitsEquiv pub mac s m).symm x
    ∀ src : SparseCallInput pub parts.2.1.val.2.2, before.val.2.2=src.compressed := by
  intro parts src
  let prior := parts.2.1.val.2.2
  let patched := written prior src.merge src.count
  obtain ⟨es,t,merge,_,_,_⟩ := entry_run (pub:=pub) (mac:=mac) parts.2.1.val.2.1 prior src.merge src.frame src.pointer
    src.length src.base src.indirect src.taskRoom src.controlRoom src.source src.apart
  obtain ⟨bs,u,mt,pack,_,effect,_⟩ := SparseExterior.prepare_run (pub:=pub) (mac:=mac) t patched src.layout src.owned
    src.root src.loaded (src.root ▸ src.frame) src.header src.initial src.independent
  have same : mt=src.compressed := funext fun a => Fin.ext (congrFun (effect.trans src.image.symm) a)
  have tail := parts.2.1.property.seq (merge.seq pack)
  have total := (Runs.block_append_iff (a := [FragmentRows.program,FragmentBucket.program])
    (b := [TypedTaskBuilder.program,CellPacket.Supplement.Batch.entry,SparseExterior.prepare])
    (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)).mpr (parts.1.property.seq tail)
  exact ((before.property.unique_of_deterministic (by decide) total).2.2).trans same

/-- Genuine stored sparse arguments for one returning preparation. Every claimed
logical cell below is tied to an occupied native compact row at its owning team.
Cells assigned elsewhere can contain arbitrary non-read data in this local memory. -/
structure SparseArgumentCells (n : ℕ) (src : SparseCallInput pub m) where
  /-- Original immutable site slots appearing in the typed packet. -/
  Slot : Type
  /-- Public sorted descriptors and one-copy private box bodies. -/
  placed : ℕ → CellPacket.Placed Slot
  /-- Physically emitted original-site equality and padding records. -/
  extra : ℕ → List Record
  /-- The compacted genuine spans followed by the actual guessed report tail. -/
  field : ℕ → SparseExterior.Field
  /-- The machine's private burst budget uses this input length. -/
  length : src.n=n
  /-- Every occupied global directory row fits. -/
  extent : let f := Frame.ofMemory pub src.compressed
    f.base+3*f.count ≤ 2^w
  /-- Byte-for-byte identification of the actual physical packet named by the task. -/
  source : ∀ i < (Frame.ofMemory pub src.compressed).count,
    readings src.compressed ((Frame.ofMemory pub src.compressed).address i)=(Frame.ofMemory pub src.compressed).team →
    src.cells i = ⟨(SparseExterior.logicalCell (placed i) (extra i) (field i)).directory,
      (placed i).privateWires,(field i).bytes⟩
  /-- The private interpreter decodes these real bytes and finishes within its assigned budget. -/
  paid : ∀ i < (Frame.ofMemory pub src.compressed).count,
    readings src.compressed ((Frame.ofMemory pub src.compressed).address i)=(Frame.ofMemory pub src.compressed).team →
    let c := SparseExterior.logicalCell (placed i) (extra i) (field i)
    c.directory.ProfileWidths ∧ SparseExterior.clock w c.directory c.privateWires (field i) ≤ n^25

/-- Restore the logical cell at every global ordinal, preserving its physical compact
payload and the exact packed-row witnesses from the real native serializer. -/
noncomputable def SparseArgumentCells.rows {n : ℕ} {src : SparseCallInput pub m} (data : SparseArgumentCells n src) :
    TypedRowsAt SparseExterior.driver n pub src.compressed := by
  let D i := (SparseExterior.logicalCell (data.placed i) (data.extra i) (data.field i)).directory
  let k i := (data.placed i).privateWires
  have placed : TypedBatch.PlacedRows pub src.compressed src.tasks src.count n (fun i => ⟨D i,k i,(data.field i).bytes⟩) := by
    refine ⟨?_,data.length ▸ src.typed.placed.cap⟩
    intro i hi belongs
    have receipt := src.typed.placed.task i hi belongs
    rw [data.source i hi belongs] at receipt
    exact receipt
  exact TypedRowsAt.ofSparseRows pub src.compressed src.tasks D k data.field src.typed.frame src.typed.width
    src.typed.base src.typed.length src.typed.space src.typed.allocated src.typed.stored src.typed.room
    src.typed.control data.extent placed data.paid

/-- The real logical input and physical bytes on the actual state preceding the
last typed writer. This can be passed to the positive packet theorem on every
native prefix, including every inconsistent claimed count or reported use. -/
theorem typedRows_on_arguments {n : ℕ} (x : Returns SignedPrep.arguments pub mac s m)
    (before : Returns SignedPrep.beforeTyped pub mac s m) :
    let parts := (argumentVisitsEquiv pub mac s m).symm x
    ∀ (src : SparseCallInput pub parts.2.1.val.2.2) (data : SparseArgumentCells n src),
      ∃ rows : TypedRowsAt SparseExterior.driver n pub before.val.2.2,
        rows.cells=(fun i => SparseExterior.logicalCell (data.placed i) (data.extra i) (data.field i)) ∧
        rows.payload=(fun i => CellSparse.Packet.input
          (SparseExterior.logicalCell (data.placed i) (data.extra i) (data.field i)).directory (data.placed i).privateWires
          (data.field i).bytes) := by
  intro parts src data
  rw [beforeTyped_memory x before src]
  exact ⟨data.rows,rfl,rfl⟩

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
