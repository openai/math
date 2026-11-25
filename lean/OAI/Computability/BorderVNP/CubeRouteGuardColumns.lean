import OAI.Computability.BorderVNP.CubeRouteEmitterInputs
import OAI.Computability.BorderVNP.PackedCableColumns

/-! # The exact source-row columns of the label and budget guards -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube Transmission Packing.Directory

variable {w R : ℕ} {a : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
variable {pins : Pins.Layout} {pub : Arg → Word w} {slotted : Memory w} {base : ℕ}
variable {I : Type*} [Fintype I] {cell : I → Fin a.cells} {id : I ↪ ℕ} {width : I → ℕ}

/-- All seven source columns fit before any group or data writer executes. -/
theorem SlottedWriter.source_words (P : SlottedWriter a D pp lp pins pub slotted base cell id width)
    (arenaFit : a.stop < 2^w) (i : Fin (D.directory pp lp).length) :
    ∀ x ∈ (D.directory pp lp)[i.val].words, x < 2^w := by
  obtain ⟨_,_,_,_,_,_,_,stop⟩ := a.writer_order
  obtain ⟨_,_,_,_,bank,_⟩ := a.separated
  apply D.populated_words_fit_of_slabs pp lp P.destinations P.fields P.tailRoom
  · rw [P.teams,← P.pinFrame.teams]
    exact (slotted _).isLt.le
  · rw [P.processors,← P.pinFrame.processors]
    exact (slotted _).isLt.le
  · have fields := P.destinations.fields
    omega
  · rw [P.literal,← P.pinFrame.literal]
    exact (slotted _).isLt
  · intro k
    rw [P.placement.entry]
    have := (cell (P.placement.key k)).isLt
    obtain ⟨_,labels,grp,own,pair,host,rec,_⟩ := a.writer_order
    omega
  · intro k
    rw [P.placement.entry,← P.placement.width_eq k]
    have h := (DataSlabs.base_end_le cell id width (P.placement.key k)).trans (P.slabs _)
    have scale := Nat.le_mul_of_pos_left a.cellStride (Nat.zero_lt_of_lt (cell (P.placement.key k)).isLt)
    change a.cellBank+a.cells*a.cellStride < 2^w at arenaFit
    exact h.trans (by omega)

/-- Match each row in the actual pre-label publication with the true receiver and width used
by the group histogram. The source slab allocation supplies the original word bounds. -/
theorem SlottedWriter.guard_columns (P : SlottedWriter a D pp lp pins pub slotted base cell id width)
    (arenaFit : a.stop < 2^w) :
    let rows := D.directory pp lp
    let frame := (pub 0).val
    let mem := ISA.publish slotted frame base rows
    let dir := LabelIndex.layout frame (readings mem)
    dir.deliveryCount=rows.length ∧ ∀ i : Fin rows.length, LabelIndex.deliveryAt dir (readings mem) i.val =
      (rows[i.val].cell,rows[i.val].width) := by
  intro rows frame mem dir
  have low := P.rawStart
  have high := P.rawEnd
  obtain ⟨hh,lab,grp,own,pair,host,rec,stop⟩ := a.writer_order
  have start : frame+9 < base := by dsimp only [frame]; omega
  have num : rows.length < 2^w := by change base+rows.length*7 ≤ _ at high; omega
  have f8 : dir.deliveries=base := by
    change readings mem (frame+8)=base
    have keep : mem (frame+8)=slotted (frame+8) := by
      rw [show mem=ISA.publish slotted frame base rows from rfl,ISA.publish,Function.update_of_ne (by omega : frame+8 ≠ frame+9),
        ISA.putWords_outside _ _ _ _ (.inl (by omega))]
    exact (congrArg Fin.val keep).trans P.pointers.1
  refine ⟨(congrArg Fin.val (ISA.publish_read slotted frame base rows start).1).trans (DiagonalResidueRAM.word_val _ _ num),?_⟩
  intro i
  have atRow := Packing.CableTriples.deliveryAt_publish slotted frame dir rows (by rw [f8]; exact start) i
    (P.source_words arenaFit i)
  rw [f8] at atRow
  exact atRow

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
