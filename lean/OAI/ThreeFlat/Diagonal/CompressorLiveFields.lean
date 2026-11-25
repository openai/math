import OAI.ThreeFlat.Diagonal.CompressorLiveGraph
import OAI.ThreeFlat.Diagonal.CompressorUnionImage

namespace OAI
/-! # Source and arrival rows of the actual, retained shrink graph -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.Graph
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Placement
open scoped BigOperators Classical Fin.NatCast
variable {B H : Type*} [AddCommGroup H] [Fintype B] [Fintype H] {w t l : ℕ}
variable (S : Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (code : B ↪ ℕ) (bound : ∀i,S.pieces i≤S.pieceRadix)
variable (lay : Bool) (hc : 2≤S.colors) (good : TagConditions P.slots (shift P) P.offset)
open private numbering_independent from OAI.ThreeFlat.Diagonal.CompressorLiveGraph

section
attribute [local irreducible] CompressorRegularize.numbering

private theorem forward_displacement (p : (B × BitWord t) × Fin (liveDegree S)) :
    (shrinkingGraph P lay S.pieces
      (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound) hc binary_neg good).displacement p =
      wireShift S P lay ((ordinalOf S P code bound lay false hc).symm p) := by
  let : LinearOrder (ShrinkEdge P S.pieces) := LinearOrder.lift' _
    (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound).injective
  simp only [shrinkingGraph, CompressorRegularize.graph, ordinalOf]
  apply congrArg (fun (number : ShrinkEdge P S.pieces ≃ (B × BitWord t) × Fin (liveDegree S)) =>
    wireShift S P lay (number.symm p))
  apply numbering_independent

end

theorem graph_shift (rev : Bool) (p : (B × BitWord t) × Fin (liveDegree S)) :
    SlotImage.shift (shrinkingGraph P lay S.pieces
      (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound) hc binary_neg good) rev p=wireShift S P lay ((ordinalOf S P code bound lay rev hc).symm p) := by
  let A := shrinkingGraph P lay S.pieces
      (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound) hc binary_neg good
  cases rev with
  | false => exact forward_displacement S P code bound lay hc good p
  | true =>
    change A.displacement (A.base.target.symm p) = _
    have far : A.base.target.symm p =
        ordinalOf S P code bound lay false hc ((ordinalOf S P code bound lay true hc).symm p) :=
      ordinal_graph S P code bound lay true hc good p
    exact (forward_displacement S P code bound lay hc good (A.base.target.symm p)).trans
      (by rw [far, Equiv.symm_apply_apply])

/-- In particular the reverse field records the same original displacement,
as required by the numerical slot image. -/
theorem graph_endpoint (rev : Bool) (p : (B × BitWord t) × Fin (liveDegree S)) :
    (SlotImage.oriented (shrinkingGraph P lay S.pieces
      (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound) hc binary_neg good) rev p).1=endpoint S P lay (!rev) ((ordinalOf S P code bound lay rev hc).symm p) ∧
    (SlotImage.oriented (shrinkingGraph P lay S.pieces
      (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound) hc binary_neg good) rev p).2=(ordinalOf S P code bound lay (!rev) hc ((ordinalOf S P code bound lay rev hc).symm p)).2 := by
  let A := shrinkingGraph P lay S.pieces
      (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound) hc binary_neg good
  change (if rev then (A).base.target.symm p else (A).base.target p).1=_ ∧
    (if rev then (A).base.target.symm p else (A).base.target p).2=_
  rw [ordinal_graph S P code bound lay rev hc good]
  exact ⟨rfl,rfl⟩


end ThreeFlat.Diagonal.CompressorPacking.Native.Graph

end OAI
