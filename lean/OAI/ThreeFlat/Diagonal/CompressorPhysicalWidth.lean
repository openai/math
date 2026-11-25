import OAI.ThreeFlat.Diagonal.CompressorRetainedWidth
import OAI.ThreeFlat.Diagonal.CompressorLiveGraph
import OAI.ThreeFlat.Diagonal.ShrinkSubdivision

namespace OAI
/-! # The width selected by a source-major RAM key is the actual regularized arc width -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.Graph
open Computability.VPVNP.Compression
open scoped Classical BigOperators
variable {B H : Type} [Fintype B] [Fintype H] [AddCommGroup H] {t l : ℕ}
variable (S : Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (code : B ↪ ℕ) (bound : ∀ i,S.pieces i≤S.pieceRadix)
variable (hc : 2≤S.colors) (lay : Bool) (good : TagConditions P.slots (shift P) P.offset)
variable (supply : P.Motif → Fin 8 → ℕ) (pad : ℕ)
set_option quotPrecheck false
local notation "order" => edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound
local notation "cover" => allPieceSlots P binary_neg good lay S.pieces order hc pad
local notation "n" => fun e=>S.pieces (typeIndex P binary_neg good lay e)
local notation "total" => fun e : CrossEdge P lay=>supply e.1 e.2
local notation "width" => SlotRefinement.actualWidth n total cover

theorem actualWidth_padding (p : Numbered B (BitWord t) (BitWord l) pad) :
    width (CompressorRefresh.unionLabels _ _ (liveDegree S) pad (.inr p))=0 := by
  change width (cover (.inr p))=0
  simp [SlotRefinement.actualWidth]

open private numbering_independent from OAI.ThreeFlat.Diagonal.CompressorLiveGraph

section
attribute [local irreducible] CompressorRegularize.numbering

private theorem source_slots_fst (p : (B × BitWord t) × Fin (liveDegree S)) (y : BitWord l) :
    ((endpointSlots P lay (fun j => (supplyRoles lay j).1) S.pieces
      (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound) hc).symm (p,y)).1 =
      (ordinalOf S P code bound lay false hc).symm p := by
  let : LinearOrder (ShrinkEdge P S.pieces) := LinearOrder.lift' _
    (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound).injective
  simp only [endpointSlots, ordinalOf]
  apply congrArg (fun (num : ShrinkEdge P S.pieces ≃ (B × BitWord t) × Fin (liveDegree S)) => num.symm p)
  apply numbering_independent

end

omit [Fintype B] [Fintype H] in
private theorem crossing_width (u : PhysicalPiece P S.pieces) :
    let b := (crossingPieces P binary_neg good lay S.pieces).symm u
    SlotEnergy.piece (supply b.1.1 b.1.2) (S.pieces (typeIndex P binary_neg good lay b.1)) b.2 =
      SlotEnergy.piece (supply u.2.1 (ShrinkMotif.survivor lay u.1)) (S.pieces u.1) u.2.2 := by
  rcases u with ⟨k, m, j⟩
  let role := crossTypeEquiv P binary_neg good lay m
  change SlotEnergy.piece (supply m (role k).val) (S.pieces (role.symm (role k)))
    (Fin.cast (congrArg S.pieces (role.symm_apply_apply k).symm) j) = _
  simp only [SlotEnergy.piece, Fin.val_cast, role, crossTypeEquiv_val, Equiv.symm_apply_apply]

theorem actualWidth_retained (p : (B × BitWord t) × Fin (liveDegree S)) (y : BitWord l) :
    let e := (ordinalOf S P code bound lay false hc).symm p
    width (CompressorRefresh.unionLabels _ _ (liveDegree S) pad (.inl (p,y))) =
      SlotEnergy.piece (supply (ShrinkWidth.sourceMotif S.pieces lay e y) (ShrinkMotif.survivor lay e.1))
        (S.pieces e.1) e.2.2 := by
  let slots := endpointSlots P lay (fun j=>(supplyRoles lay j).1) S.pieces order hc
  let lanes := pieceLanes P S.pieces
  let crossing := crossingPieces P binary_neg good lay S.pieces
  let unit := lanes (slots.symm (p,y))
  let bundle := crossing.symm unit
  have covered : cover (.inl bundle)=CompressorRefresh.unionLabels _ _ (liveDegree S) pad (.inl (p,y)) := by
    change CompressorRefresh.unionLabels _ _ (liveDegree S) pad (.inl (slots (lanes.symm (crossing bundle)))) = _
    rw [show crossing bundle = unit from crossing.apply_symm_apply unit,
      show lanes.symm unit = slots.symm (p,y) from lanes.symm_apply_apply _,
      slots.apply_symm_apply]
  let e := (ordinalOf S P code bound lay false hc).symm p
  let z := y-(slotSite P lay (fun j=>(supplyRoles lay j).1) e).2.2
  have first : (slots.symm (p,y)).1 = e := source_slots_fst S P code bound hc lay p y
  have unpack : slots.symm (p,y) = (e,z) := by
    apply Prod.ext first
    change y - (slotSite P lay (fun j=>(supplyRoles lay j).1) (slots.symm (p,y)).1).2.2 = z
    rw [first]
  have unitEq : unit = ⟨e.1, ShrinkWidth.sourceMotif S.pieces lay e y, e.2.2⟩ := by
    change lanes (slots.symm (p,y)) = _
    rw [unpack]
    rfl
  rw [←covered]
  unfold SlotRefinement.actualWidth
  rw [Equiv.symm_apply_apply]
  refine (crossing_width S P lay good supply unit).trans ?_
  rw [unitEq]


end ThreeFlat.Diagonal.CompressorPacking.Native.Graph

end OAI
