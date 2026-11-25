import OAI.Computability.BorderVNP.PackedGridReportedUse
import OAI.Computability.BorderVNP.DiagonalInitialGridBundle
import OAI.Computability.BorderVNP.PackedGridExternal

/-! # Actual selected bits through conditioned initial grid boxes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.PowerWords

open Crossing
open scoped Classical
variable {D b : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits}
    {Team Param Gadget : Type*} [Fintype Team] [Fintype Param]
    {tags : N.Tables (Entry Param Gadget)} (words : PowerWords Team Param Gadget b N tags)
variable {Cell Q : Type} [Fintype Cell] [DecidableEq Cell] [Fintype Q]
    (cell : N.Site → Cell) (position : Cell → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (hidden : ∀ i, N.InsideAssignment cell i) {src dst : Q → Cell} {H : ℕ}
    (packing : (N.cellNetwork cell position).ChannelPacking src dst H)

/-- At a surviving physical cell, each selected bit is read from the original fine
owner, on the unpacked public subwords and this exact hidden private assignment. -/
theorem grid_selected_eq (v : Cell) (a x) (slot : PowerSlot Team Param b)
    (hp : conditionedGridTags cell position packing tags hidden v a x ≠ 0) :
    (words.gridWords cell position hidden packing).selected v a x slot =
      unpackFactor packing (words.hosted cell position hidden) v a x slot := by
  have ok : padOK packing v a x := by
    by_contra h
    exact hp (by simp [conditionedGridTags,paddedFactor,h])
  have alive : unpackFactor packing (conditionedCellTags cell position tags hidden) v a x ≠ 0 := by
    simpa only [conditionedGridTags,paddedFactor,ite_eq_left ok] using hp
  unfold gridWords paddedWords
  simp only [ite_eq_left ok]
  unfold unpackFactor at alive ⊢
  simp only [cellWords,ite_eq_left alive]

/-- At its actual fine owner, a surviving public cell reads the individual slot's
selected bit, with no summation over other unary occurrences in the cell. -/
theorem grid_owner_selected (slot : PowerSlot Team Param b)
    (a : {q : Q // src q = cell (words.site slot) ∨ dst q = cell (words.site slot)} → Fin H → Bool)
    (x : ∀ p : {p : P // cell (N.attach p) = cell (words.site slot)}, Fin (bits p.val) → Bool)
    (hp : conditionedGridTags cell position packing tags hidden (cell (words.site slot)) a x ≠ 0) :
    (words.gridWords cell position hidden packing).selected (cell (words.site slot)) a x slot =
      fineFactor cell words.selected (cell (words.site slot)) (hidden _) ⟨words.site slot,rfl⟩
        (fun e i => a ⟨packing.channel e.val, e.property.imp
          ((packing.src_eq e.val).trans) ((packing.dst_eq e.val).trans)⟩ (packing.address ⟨e.val,i⟩).2) x slot := by
  rw [grid_selected_eq words cell position hidden packing _ _ _ _ hp]
  simp only [unpackFactor,hosted,dite_true]

/-- The shared bottom bundle preserves the independently chosen physical word of
each copy, including false uses at a passing site. -/
theorem repeat_selected_eq {copies : ℕ} {tags' : Fin copies → N.Tables (Entry Param Gadget)}
    (parts : ∀ i, PowerWords Team Param Gadget b N (tags' i)) (v : N.Site) (a x)
    (slot : PowerSlot (Fin copies × Team) Param b) (hp : repeatedTags tags' v a x ≠ 0) :
    (repeated tags' parts).selected v a x slot =
      gridSlice slot.1.1 (parts slot.1.1).selected v a x (slot.1.2,slot.2) := by
  simp only [repeated,ite_eq_right hp]

end Diagonal.CellEntries.PowerWords

end BorderVNP
end Computability
end OAI
