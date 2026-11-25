import OAI.Computability.BorderVNP.RoutingISAScheduleClockProducedInput

/-! # Occupied task rows on the physical signed sparse argument source -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellDispatch CellPacket CellPacket.Supplement.Batch TypedTaskBuilder

variable {w n : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
    {Site : Type}

/-- The occupied rows and disjoint memory intervals of a native task source.
All equalities specify physical data produced by the builder and sparse writer. -/
structure ProducedRoster (a : SignedTaskArena.Layout) (l : CellControlRows.Layout) (raw : ℕ → ℕ)
    (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record) (src : SparseCallInput pub m) : Prop where
  fields : l.toLayout.Fields raw
  room : l.toLayout.Room raw w
  span : ∀ c < l.cells, raw (l.sorted+l.padded+(l.stops+c))-raw (l.sorted+l.padded+c)-1=3*((p c).parts.length+3)
  frameLow : l.frame+16≤l.sorted ∧ l.frame+16≤l.merged
  callsHigh : l.sorted+l.padded≤l.calls ∧ l.merged+l.cells≤l.calls
  merge : src.merge=(fun i => (produced l raw p geom extra i).cell)
  count : src.count=l.before raw l.cells
  layout : src.layout=SparseExterior.batchLayout a l.frame l.control src.count
  globals : ∀ i < src.count, (src.owned i).global<a.fragments.cells
  widths : ∀ i < src.count, (src.owned i).field.bytes.length≤a.fragments.stride
  early : l.frame+112≤a.fragments.external
  /-- Physical starts of the compressed tasks' call, scratch and burst arrays. -/
  taskArena : l.toLayout.Arenas raw w src.tasks

/-- Every source obtained by the native supplemental and compressed-row constructor
has the roster it actually encoded. Compact ordinals are decoded in the original
global order by the task producer. -/
theorem SparseCallInput.ofOwned_roster (a : SignedTaskArena.Layout) (l : CellControlRows.Layout) (raw : ℕ → ℕ)
    (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record) (cells : ℕ → SparseExterior.Owned)
    {fp fields room image word hdr fourRoom table four callBase cellCount reportCount controller span frameLow callsHigh
      controlLo controlHi ctrlSorted ctrlMerged early mergeFields ranges global extent spans tails inputs intervals region arenas cap} :
    ProducedRoster a l raw p geom extra (SparseCallInput.ofOwned (n:=n) pub mac s m a l raw p geom extra cells fp fields
      room image word hdr fourRoom table four callBase cellCount reportCount controller span frameLow callsHigh controlLo
      controlHi ctrlSorted ctrlMerged early mergeFields ranges global extent spans tails inputs intervals region arenas cap) := by
  refine ⟨fields,room,span,⟨by omega,by omega⟩,callsHigh,rfl,rfl,rfl,?_,?_,early,arenas⟩
  · intro i hi
    have h := (global_spec l.toLayout raw hi).1
    change (cells (globalCell l.toLayout raw i)).global<a.cube.cells
    rw [global _ h (global_spec l.toLayout raw hi).2.1,←cellCount]
    exact h
  · intro i hi
    exact extent _ (global_spec l.toLayout raw hi).1 (global_spec l.toLayout raw hi).2.1

/-- The same compact global ordinals for a fully populated source array. -/
theorem SparseCallInput.ofProduced_roster (a : SignedTaskArena.Layout) (l : CellControlRows.Layout) (raw : ℕ → ℕ)
    (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record) (cells : ℕ → SparseExterior.Owned)
    {fp fields room image word hdr fourRoom table four callBase cellCount reportCount controller span frameLow callsHigh
      controlLo controlHi ctrlSorted ctrlMerged early mergeFields ranges global extent spans tails inputs intervals region arenas cap} :
    ProducedRoster a l raw p geom extra (SparseCallInput.ofProduced (n:=n) pub mac s m a l raw p geom extra cells fp fields
      room image word hdr fourRoom table four callBase cellCount reportCount controller span frameLow callsHigh controlLo
      controlHi ctrlSorted ctrlMerged early mergeFields ranges global extent spans tails inputs intervals region arenas cap) :=
  SparseCallInput.ofOwned_roster a l raw p geom extra cells

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
