import OAI.Computability.BorderVNP.DiagonalNativeCellRoster
import OAI.Computability.BorderVNP.CellSparseExteriorSupplementalCost
import OAI.Computability.BorderVNP.PackedFinalCellClock
import OAI.Computability.BorderVNP.CoverAddressCoding

/-! # Private sparse packet sources at the genuine owned global cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open VPVNP.BurstRAM CellDispatch TypedTaskBuilder CellPacket CellSparse
open BorderVNP.Packing BorderVNP.Packing.Inherited CompactMachine
open private record_unique from OAI.Computability.BorderVNP.CoverAddressCoding

/-- Logical private input on a sparse owned row. The supplemental records extend
the original typed directory, and the private routine decodes the physical exterior. -/
def logicalCell {Site : Type} (p : Placed Site) (extra : List Record) (field : Field) : CellInput :=
  ⟨BottomReports.appendRows p.directory extra,p.privateWires,field.values⟩

/-- The exact original packet part (before the exterior delimiter) of a supplemented
task. This uses injectivity of the self-delimiting word encoder on the full payload. -/
theorem supplemented_packet {Site : Type} (p : Placed Site) (extra : List Record)
    (l : Supplement.Layout) (geom : ℕ) :
    (Supplement.task l p geom extra).packet = Packet.bits (BottomReports.appendRows p.directory extra) p.privateWires := by
  have encoded := Supplement.payload_eq l p geom extra
  exact (record_unique _ _ _ _ encoded).1

/-- Recover the real compact ordinal for an owned cell, its call row, complete
spliced directory before the exterior delimiter, and the very field read by its
private routine. The predecessor's roster is the native task builder's output. -/
theorem produced_ordinals {Site : Type} {w : ℕ} {pub : Arg → Word w} {m : Memory w}
    (l : CellControlRows.Layout) (src : ℕ → ℕ) (p : ℕ → Placed Site) (geom : ℕ → ℕ)
    (extra : ℕ → List Record) (external : ℕ → Owned)
    (table : OwnerTable pub m ⟨l.team,l.calls,l.cells⟩ (l.owner src))
    {i : ℕ} (hi : i < (Frame.ofMemory pub m).count)
    (mine : readings m ((Frame.ofMemory pub m).address i)=(Frame.ofMemory pub m).team) :
    let original := fun j => (Supplement.Batch.produced l src p geom extra j).typed
    let owned := fun j => external (globalCell l.toLayout src j)
    ∃ j < l.before src l.cells, (original j).callRow=(Frame.ofMemory pub m).address i ∧
      (original j).cell.packet=Packet.bits (logicalCell (p i) (extra i) (external i).field).directory (p i).privateWires ∧
      (owned j).field=(external i).field := by
  intro original owned
  rw [table.frame] at hi mine ⊢
  have h : l.owner src i=l.team := (table.atRow i hi).symm.trans mine
  let j := l.before src i
  have eqn := global_at l.toLayout src hi h
  refine ⟨j,l.before_strict src hi h,?_,?_,?_⟩
  · change l.call (globalCell l.toLayout src j) = i*3+l.calls
    rw [eqn]; simp [TypedTaskBuilder.Layout.call,Nat.mul_comm,Nat.add_comm]
  · change (Supplement.task _ (l.atCell src p (globalCell l.toLayout src j)) _ (extra (globalCell l.toLayout src j))).packet = _
    rw [supplemented_packet,eqn]
    rfl
  · change (external (globalCell l.toLayout src j)).field=_
    rw [eqn]

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
