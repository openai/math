import OAI.ThreeFlat.Diagonal.ShrinkSupplyRequestValues

namespace OAI
/-! # The four native fields of a supply request -/

namespace ThreeFlat.Diagonal.CompressorPacking.SupplySend

open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression HistoryContraction MotifOuterTerms MotifKernel MotifBinaryPacking
open scoped Classical
noncomputable section

variable {c d : ℕ} {V H Tag L F : Type} [Field F]
    [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
    (P : PackingData V H Tag L d c)
    (base : P.Motif → Fin 2 → ℕ) (r : P.Motif → ℕ)
    (T : ∀ m, FixedMotifTile demandGraph supplyGraph (base m) F)
    (x : Histories P base r T) (hn : ∀ a : Tag, -a = a)
    (good : TagConditions P.slots (shift P) P.offset) (lay : Bool)
    (n : Fin 4 → ℕ) (positive : ∀ i, 0 < n i) (order : ShrinkEdge P n ↪ ℕ)
    (hc : 2 ≤ c) (pad : ℕ) (padding : LiftedSlots (V × Tag) pad L)

/-- A crossing bit addresses a numbered half-edge. An absorbed bit addresses
its original edge and bit within the motif. -/
def fieldValues (width : P.Motif → Fin 8 → ℕ)
    (G : LiftedSlots (V × Tag) (usedDegree n c d + pad) L)
    (m : P.Motif) (u : Fin 6) (edge : Fin 8) (bit : Fin (width m edge)) : Fin 4 → ℕ :=
  if h : wireOwner supplyGraph.tail supplyGraph.head (partySite P lay m) edge = none then
    let wire : CrossEdge P lay := ⟨m,⟨edge,h⟩⟩
    let kind := typeIndex P hn good lay wire
    let part := (SlotEnergy.pieceIndex (width m edge) (n kind) (positive kind)).symm bit
    let arc := allPieceSlots P hn good lay n order hc pad (.inl ⟨wire,part.1⟩)
    ![2,0,halfOrdinal G arc (decide (u ≠ ShrinkMotif.supplySrc edge)),part.2.val]
  else ![3,edge.val,bit.val,0]

private theorem crossingFields {Arc : Type} (number : Arc → Bool → ℕ)
    {issued selected : Arc} {fromSide toSide : Bool} {fromBit toBit : ℕ}
    (arc : issued = selected) (side : fromSide = toSide) (bit : fromBit = toBit) :
    (![2,0,number selected toSide,toBit] : Fin 4 → ℕ) =
      ![2,0,number issued fromSide,fromBit] := by
  cases arc
  cases side
  cases bit
  rfl

/-- At a crossing, all four fields agree with the request made to the successor graph. -/
theorem fieldValues_request (G : LiftedSlots (V × Tag) (usedDegree n c d + pad) L)
    (v : Site V Tag L) (m : P.Motif) (party : {u // partySite P lay m u = v})
    (q : supplyGraph.Port party.val)
    (cross : wireOwner supplyGraph.tail supplyGraph.head (partySite P lay m) q.val.1 = none)
    (j : Fin (historyWidth P base r T x m q.val.1)) :
    let req := request P base r T x hn good lay n positive order hc pad padding v m
      (PrivateOrder.onSide party q cross) j
    fieldValues P hn good lay n positive order hc pad (historyWidth P base r T x) G
        m party.val q.val.1 j =
      ![2,0,halfOrdinal G req.1.val.1 req.1.val.2,req.2.val] := by
  have fields := request_values P base r T x hn good lay n positive order hc pad padding
    v m party q cross j
  dsimp only
  rw [fieldValues, dite_eq_left cross]
  exact crossingFields (halfOrdinal G) fields.1 fields.2.1 fields.2.2


end
end ThreeFlat.Diagonal.CompressorPacking.SupplySend

end OAI
