import OAI.Computability.BorderVNP.CellSparseExteriorDriver

/-! # Physical and logical cell arguments for the finite-field evaluator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Cells

open VPVNP.BurstRAM RoutingISA TypedBatch CellDispatch CompactMachine CellMacro.Generator CellSparse

/-- The library has a fixed decoder for its argument representation. For
sparse inputs, the per-cell fields describe the real bytes and the logical
values in the proof of that fixed decoder's execution. -/
inductive Codec where
  /-- Input bytes are exactly the supplied logical values. -/
  | dense
  /-- The logical values are restored from true intervals and the raw report suffix. -/
  | sparse (fields : ℕ → SparseExterior.Field)

/-- The decoder is fixed for each physical input format. -/
noncomputable def Codec.driver : Codec → Fragment IO
  | .dense => cellDriver
  | .sparse _ => SparseExterior.driver

/-- Original directory with the exterior bytes actually present in the fetched argument. -/
def Codec.physical : Codec → (ℕ → CellInput) → ℕ → CellInput
  | .dense, cells => cells
  | .sparse fields, cells => fun i => {cells i with external := (fields i).bytes}

/-- The private clock and the identification of the logical assignment on a real owned row. -/
def Codec.Valid (codec : Codec) (w n : ℕ) (c : CellInput) (i : ℕ) : Prop :=
  c.directory.ProfileWidths ∧ match codec with
  | .dense => cellClock w c ≤ n^25
  | .sparse fields => SparseExterior.clock w c.directory c.privateWires (fields i) ≤ n^25 ∧ (fields i).values=c.external

/-- Executed bytecode, using the field restored by the chosen native decoder. -/
private noncomputable def Codec.ops : Codec → CellInput → ℕ → List CellMacro.Op
  | .dense, c, _ => c.stmt.expand []
  | .sparse fields, c, i => (withExternal (fields i).values (c.directory.program c.privateWires)).expand []

private theorem Codec.packed {w table count n : ℕ} {pub : Arg → Word w} {m : Memory w}
    {tasks : ℕ → Task} (codec : Codec) (cells : ℕ → CellInput) (hw : 0 < w)
    (placed : PlacedRows pub m tasks count n (codec.physical cells)) (alloc : Allocated w table count tasks)
    (room : ∀ i < count, (tasks i).cell.Room w) (ctrl : ControlLayout pub m tasks count)
    (valid : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val=(Frame.ofMemory pub m).team →
      codec.Valid w n (cells i) i) :
    PackedRows (Frame.ofMemory pub m) (written m tasks count) codec.driver n
      (fun i => Packet.input (cells i).directory (cells i).privateWires ((codec.physical cells i).external))
      (fun i => codec.ops (cells i) i) := by
  cases codec with
  | dense => exact concretePackedRows hw placed alloc room ctrl valid
  | sparse fields =>
    exact SparseExterior.packedRows (fun i => (cells i).directory) (fun i => (cells i).privateWires) fields
      hw placed alloc room ctrl (fun i hi own => ⟨(valid i hi own).1,(valid i hi own).2.1⟩)

private theorem Codec.logical {w n : ℕ} (codec : Codec) (c : CellInput) (i : ℕ) (valid : codec.Valid w n c i) :
    CellMacro.value (codec.ops c i) ⟨true,false⟩ [] = c.weight := by
  cases codec with
  | dense => exact value_external_directory ..
  | sparse fields =>
    change CellMacro.value ((withExternal (fields i).values (c.directory.program c.privateWires)).expand []) _ [] = _
    rw [valid.2.2]
    exact value_external_directory ..

/-- True paths and clock of the finite team's physical packet preparation and
signed private calls, with values taken on the restored logical exterior. -/
theorem Codec.team_value (codec : Codec) {w table count n : ℕ} (pub : Arg → Word w) (s : Bank w) (m : Memory w)
    (tasks : ℕ → Task) (cells : ℕ → CellInput) (routines : TeamOpcode.Macros w 8)
    (frame : (pub 0).val+90 < 2^w) (width : (m ((pub 0).val+30)).val=w)
    (base : (m ((pub 0).val+89)).val=table) (len : (m ((pub 0).val+90)).val=count)
    (space : table+7*count ≤ 2^w) (layout : Allocated w table count tasks)
    (source : ∀ i < count, (tasks i).Stored m table i ∧ (tasks i).cell.Stored m)
    (room : ∀ i < count, (tasks i).callRow+2 < 2^w ∧ (tasks i).cell.Room w)
    (control : ControlLayout pub m tasks count) (placed : PlacedRows pub m tasks count n (codec.physical cells))
    (directory : (Frame.ofMemory pub m).base+3*(Frame.ofMemory pub m).count ≤ 2^w)
    (privateData : ∀ i < (Frame.ofMemory pub m).count,
      (m ((Frame.ofMemory pub m).address i)).val=(Frame.ofMemory pub m).team →
      codec.Valid w n (cells i) i) :
    let mac := install codec.driver n routines
    let f := Frame.ofMemory pub m
    let mt := written m tasks count
    ∃ pre t, Runs pub mac entry s m pre t mt ∧
      traceCost pre ≤ loadDirectory.slots+TypedBatch.setup.slots+(∑ j ∈ Finset.range count, rowCharge (fun k => (tasks k).cell.cost w) j)+1 ∧
      let paths := CompactBatch.preparedHistories pre f pub mt (choices codec.driver n)
      (∀ bits es, TeamRAM.execute (runCells.program.fetch pub mac) ⟨0,s⟩ m bits = some es ↔
        es ∈ paths ∧ es.map TeamRAM.Event.choices = bits) ∧
      (∀ es ∈ paths, TeamContraction.Within (traceCost pre + (17+7*f.count+4*(f.ownedRows mt 0 f.count).length +
        ∑ j ∈ Finset.range count, ((tasks j).cell.burst w).length)) (TeamScales.width n (1/2)) (n^25) es) ∧
      ∑ es ∈ paths, (es.map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod =
        ((f.ownedRows m 0 f.count).map (fun i => (cells i).weight)).prod := by
  intro mac f mt
  obtain ⟨pre,t,prep,cost,_⟩ := entry_run pub mac s m tasks frame width base len space layout source room
  obtain ⟨ff,owners⟩ := control.survives
  change Frame.ofMemory pub mt=f at ff
  change ∀ i < f.count, mt (f.address i)=m (f.address i) at owners
  have hw : 0<w := by cases w with
    | zero => simp at frame
    | succ => omega
  have packed := codec.packed cells hw placed layout (fun i hi => (room i hi).2) control privateData
  refine ⟨pre,t,prep,cost,?_,prepared_within codec.driver routines placed layout (fun i hi => (room i hi).2) control prep,?_⟩
  · intro bits es
    have endRoom : (Frame.ofMemory pub mt).base + 3*(Frame.ofMemory pub mt).count ≤ 2^w := ff ▸ directory
    rw [←ff]
    exact CompactBatch.mem_prepared_iff_of (by decide : entry.deterministic=true)
      (by decide : entry.withoutAccept=true) prep (mem_choices codec.driver n routines) (by omega) endRoom
  · rw [CompactBatch.sum_prepared_of (by decide : entry.unsigned=true) prep,CompactMachine.sum_directory pub _ n packed]
    have same : f.ownedRows mt 0 f.count = f.ownedRows m 0 f.count := by
      apply List.filter_congr
      intro i hi
      rw [owners i (by simpa using hi)]
    rw [same]
    congr 1
    apply List.map_congr_left
    intro i hi
    have mem := List.mem_filter.mp hi
    exact codec.logical (cells i) i (privateData i (by simpa using mem.1) (of_decide_eq_true mem.2))

end FiniteEvaluator.Cells

end BorderVNP
end Computability
end OAI
