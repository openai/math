import OAI.Computability.BorderVNP.CellSparseExteriorTyped
import OAI.Computability.BorderVNP.CellTeamSupplementalClock

/-! # Charging the supplemental initializer after native exterior compression -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open VPVNP.BurstRAM CellPacket CellSparse Cube.TeamRowClock

variable {Site : Type} {w : ℕ}

/-- The cell placement used by the initializer after the sparse pass publishes
the address and length of its encoded field. -/
def Owned.placed (o : Owned) (l : Layout) (p : Placed Site) : Placed Site :=
  { p with externalBase := o.dest l, external := o.field.bytes }

/-- Updating the exterior preserves the typed public and original-site parts. -/
theorem Owned.placed_parts (o : Owned) (l : Layout) (p : Placed Site) :
    (o.placed l p).parts = p.parts := rfl

/-- The compressed placements still describe the cells in the live geometry sort. -/
theorem supplemental_shape {S : Type} {C : ℕ} {D : CellPacketGeometry.SiteWords.Directory S Site C}
    (l : Layout) (o : Fin C → Owned) (p : Fin C → Placed Site) (shape : TypedBatch.SourceShape p D) :
    TypedBatch.SourceShape (fun c => (o c).placed l (p c)) D :=
  ⟨shape.privateWires,shape.boxes,shape.records,shape.reports⟩

/-- The supplemental task in the same compact slot after publishing its sparse field. -/
def Owned.supplemental (o : Owned) (l : Layout) (src : Supplement.Batch.Owned Site) :
    Supplement.Batch.Owned Site :=
  { src with placed := o.placed l src.placed }

/-- Its seven-word initializer is exactly the task whose row and sources were
established by the native sparse writer. -/
theorem Owned.supplemental_typed (o : Owned) (l : Layout) (src : Supplement.Batch.Owned Site) :
    (o.supplemental l src).typed = o.typed l src.typed := rfl

/-- The compact ordinal selects both the true original supplemental task and
the exterior encoded for its global cell. -/
noncomputable def supplementalRow (l : CellControlRows.Layout) (mem : ℕ → ℕ) (sl : Layout)
    (cells : ℕ → Owned) (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List Record)
    (i : ℕ) : Supplement.Batch.Owned Site :=
  (cells (TypedTaskBuilder.globalCell l.toLayout mem i)).supplemental sl
    (Supplement.Batch.produced l mem p geom extra i)

/-- Read the compact task row, encoded bytes, and original chunk sources from the
native sparse pass's output. The prepass only supplies the old row and its geometry. -/
theorem produced_stored_after (l : CellControlRows.Layout) (mem : ℕ → ℕ) (sl : Layout)
    (cells : ℕ → Owned) (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List Record)
    (before after : Memory w) (i : ℕ) (hi : i < sl.count) :
    let owned := fun j => cells (TypedTaskBuilder.globalCell l.toLayout mem j)
    let tasks := fun j => (Supplement.Batch.produced l mem p geom extra j).typed
    readings after = written sl owned (readings before) sl.count →
      Protected sl owned tasks →
      (tasks i).Stored before sl.tasks i →
      WordsAt (readings before) (tasks i).cell.descriptorBase (descriptors (tasks i).cell.chunks) →
      (∀ c ∈ (tasks i).cell.chunks, c.Stored (readings before)) →
      let task := (supplementalRow l mem sl cells p geom extra i).typed
      task.Stored after sl.tasks i ∧ task.cell.Stored after := by
  intro owned tasks post safe row desc chunks
  exact stored_after sl owned tasks before after post safe i hi row desc chunks

/-- Sum the compressed task units in their physical row order. Relocation of the
descriptor, scratch, and burst addresses does not affect the global cell charge. -/
theorem produced_units (l : CellControlRows.Layout) (mem : ℕ → ℕ) (sl : Layout)
    (cells : ℕ → Owned) (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List Record)
    (w description : ℕ) :
    let rows := supplementalRow l mem sl cells p geom extra
    (∑ i ∈ Finset.range (l.before mem l.cells), Supplement.units (rows i).placed (rows i).extra w description) =
      assignedSum (fun c : Fin l.cells => l.owner mem c.val) l.team
        (fun c => Supplement.units ((cells c.val).placed sl (p c.val)) (extra c.val) w description) := by
  intro rows
  rw [←Fin.sum_univ_eq_sum_range]
  exact TypedTaskBuilder.sum_owned l.toLayout mem
    (fun c => Supplement.units ((cells c).placed sl (p c)) (extra c) w description)

/-- Bound the supplemental prepass, typed initializer, and dispatch using the
stored sources of the compressed cells and the exact global owner-indexed sum. -/
theorem produced_nativeCharge_le (l : CellControlRows.Layout) (mem : ℕ → ℕ) (sl : Layout)
    (cells : ℕ → Owned) (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List Record)
    (description : ℕ) (f : CellDispatch.Frame) (m mt : Memory w) (hw : 0<w)
    (stored : ∀ i < l.before mem l.cells, (supplementalRow l mem sl cells p geom extra i).typed.cell.Stored m)
    (body : ∀ c < l.cells, l.owner mem c=l.team → ∀ j,
      (p c).headerWidth+(Packet.Source.boxBody ((p c).factors j)).length ≤ description) :
    Supplement.Batch.nativeCharge (supplementalRow l mem sl cells p geom extra) f mt (l.before mem l.cells) ≤
      64+11*f.count+100*(l.before mem l.cells)+308*(assignedSum (fun c : Fin l.cells => l.owner mem c.val) l.team
        (fun c => Supplement.units ((cells c.val).placed sl (p c.val)) (extra c.val) w description)) := by
  rw [←produced_units l mem sl cells p geom extra w description]
  apply Supplement.Batch.nativeCharge_of_stored m _ description f mt hw stored
  intro i hi
  obtain ⟨hc,ho,_⟩ := TypedTaskBuilder.global_spec l.toLayout mem hi
  exact body _ hc ho

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
