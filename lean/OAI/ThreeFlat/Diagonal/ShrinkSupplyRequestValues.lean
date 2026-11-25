import OAI.ThreeFlat.Diagonal.ShrinkSupplySend

namespace OAI
/-! # The three values carried by a crossing supply request -/

namespace ThreeFlat.Diagonal.CompressorPacking.SupplySend

open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression HistoryContraction MotifOuterTerms MotifKernel MotifBinaryPacking
open scoped Classical
noncomputable section

private theorem piece_value_congr {Edge Label : Type} (width count : Edge → ℕ)
    (positive : ∀ e, 0 < count e) (number : (Σ e, Fin (count e)) → Label)
    {before after : Edge} (same : before = after) (j : Fin (width after)) :
    let left := (SlotEnergy.pieceIndex (width before) (count before) (positive before)).symm
      (Fin.cast (congrArg width same).symm j)
    let right := (SlotEnergy.pieceIndex (width after) (count after) (positive after)).symm j
    number ⟨before,left.1⟩ = number ⟨after,right.1⟩ ∧ left.2.val = right.2.val := by
  cases same
  exact ⟨rfl,rfl⟩

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

/-- The emitted arc, endpoint side and residual bit use the original crossing wire
and the balanced piece containing the selected history bit. -/
theorem request_values (v : Site V Tag L) (m : P.Motif)
    (party : {u // partySite P lay m u = v}) (q : supplyGraph.Port party.val)
    (cross : wireOwner supplyGraph.tail supplyGraph.head (partySite P lay m) q.val.1 = none)
    (j : Fin (historyWidth P base r T x m q.val.1)) :
    let wire : CrossEdge P lay := ⟨m,⟨q.val.1,cross⟩⟩
    let kind := typeIndex P hn good lay wire
    let part := (SlotEnergy.pieceIndex (historyWidth P base r T x m q.val.1)
      (n kind) (positive kind)).symm j
    let req := request P base r T x hn good lay n positive order hc pad padding v m
      (PrivateOrder.onSide party q cross) j
    req.1.val.1 = allPieceSlots P hn good lay n order hc pad (.inl ⟨wire,part.1⟩) ∧
      req.1.val.2 = decide (party.val ≠ ShrinkMotif.supplySrc q.val.1) ∧
      req.2.val = part.2.val := by
  let a := PrivateOrder.onSide party q cross
  let wire : CrossEdge P lay := ⟨m,⟨q.val.1,cross⟩⟩
  let port := incidentPort (fun _ : P.Motif => supplyGraph) (partySite P lay) v m a
  have edge : port.val.1 = wire :=
    incidentPort_edge (fun _ : P.Motif => supplyGraph) (partySite P lay) v m a
  have moved := piece_value_congr (bitsOn P base r T x lay) (divisions P hn good lay n)
    (fun e => positive (typeIndex P hn good lay e))
    (fun piece => allPieceSlots P hn good lay n order hc pad (.inl piece)) edge j
  have issued := request_fields P base r T x hn good lay n positive order hc pad padding v m a j
  exact ⟨(congrArg Prod.fst issued.1).trans moved.1,
    (congrArg Prod.snd issued.1).trans (supplySide P lay v m party q cross),
    issued.2.trans moved.2⟩


end
end ThreeFlat.Diagonal.CompressorPacking.SupplySend

end OAI
