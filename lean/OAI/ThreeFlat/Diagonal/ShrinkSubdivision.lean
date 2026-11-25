import OAI.ThreeFlat.Diagonal.ShrinkCrossings
import OAI.ThreeFlat.Diagonal.PaddedSlotNumbering
import OAI.ThreeFlat.Diagonal.ParallelSlotRewrite

namespace OAI
/-! # Subdivide the grouped six-party crossing graph onto the regular lifted slots -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks HistoryContraction
open scoped Classical BigOperators
noncomputable section

variable {c d : ℕ} {V H Tag L : Type}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable (P : PackingData V H Tag L d c)
variable (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset)
variable (layout : Bool) (n : Fin 4 → ℕ) (order : ShrinkEdge P n ↪ ℕ) (hc : 2 ≤ c)

abbrev Numbered (V Tag L : Type) (d : ℕ) := ((V × Tag) × Fin d) × L

def slotPortGraph {k : ℕ} (G : LiftedSlots (V × Tag) k L) :
    PortGraph (Site V Tag L) (Numbered V Tag L k) :=
  ⟨numberedSite, fun e => numberedSite (G.actualTarget e)⟩

/-- Source numbers of all crossing pieces on the used-degree subgraph. -/
def pieceSlots :
    (Σ e : CrossEdge P layout, Fin (n (typeIndex P hn good layout e))) ≃
      Numbered V Tag L (usedDegree n c d) :=
  (crossingPieces P hn good layout n).trans ((pieceLanes P n).symm.trans
    (endpointSlots P layout (fun t => (supplyRoles layout t).1) n order hc))

/-- Number the genuinely retained crossing pieces first, then the padding arcs. -/
def allPieceSlots (pad : ℕ) :
    ((Σ e : CrossEdge P layout, Fin (n (typeIndex P hn good layout e))) ⊕ Numbered V Tag L pad) ≃
      Numbered V Tag L (usedDegree n c d + pad) :=
  ((pieceSlots P hn good layout n order hc).sumCongr (Equiv.refl _)).trans
    (CompressorRefresh.unionLabels (V × Tag) L _ pad)

theorem physical_ends (pad : ℕ) (padding : LiftedSlots (V × Tag) pad L) (e : CrossEdge P layout)
    (i : Fin (n (typeIndex P hn good layout e))) (side : Bool) :
    (slotPortGraph (CompressorRefresh.union (shrinkingGraph P layout n order hc hn good) padding)).vertex
      (allPieceSlots P hn good layout n order hc pad (.inl ⟨e,i⟩)) side =
      (MotifKernel.crossGraph (fun _ : P.Motif => supplyGraph) (partySite P layout)).vertex e side := by
  let x := crossingPieces P hn good layout n ⟨e,i⟩
  let p := (pieceLanes P n).symm x
  let src := fun t => (supplyRoles layout t).1
  let dst := fun t => (supplyRoles layout t).2
  rw [crossing_site P hn good layout e side]
  cases side with
  | false =>
    change numberedSite (CompressorRefresh.unionLabels _ L _ pad (.inl (endpointSlots P layout src n order hc p))) = _
    exact endpoint_site P layout src n order hc x
  | true =>
    change numberedSite ((CompressorRefresh.union _ padding).actualTarget
      (CompressorRefresh.unionLabels _ L _ pad (.inl (endpointSlots P layout src n order hc p)))) = _
    rw [CompressorRefresh.union_actual_left, endpoint_target P layout n order hc hn good x]
    exact endpoint_site P layout dst n order hc x

/-- A zero-width arc for every pad and one balanced interval on each numbered
crossing piece give a successor shape with the actual public target permutation. -/
def slotLabels (b : CrossEdge P layout → ℕ) (pad : ℕ)
    (a : Numbered V Tag L (usedDegree n c d + pad)) : Type :=
  Fin (2^SlotRefinement.actualWidth (fun e => n (typeIndex P hn good layout e)) b
    (allPieceSlots P hn good layout n order hc pad) a)

/-- Local read and boundary bijection for numbering the grouped crossing graph.
This can be applied directly to the original term-dependent rewrite's targets. -/
def subdivisionRefines
    (I : P.Motif → Fin 8 → Type) [∀ m e, Fintype (I m e)] [∀ m e, Inhabited (I m e)]
    (b : CrossEdge P layout → ℕ) (encode : ∀ e : CrossEdge P layout, I e.1 e.2 ≃ Fin (2^b e))
    (positive : ∀ t, 0 < n t) (pad : ℕ) (padding : LiftedSlots (V × Tag) pad L) :
    SlotRefinement.Refines (MotifKernel.crossGraph (fun _ : P.Motif => supplyGraph) (partySite P layout))
      (fun e => I e.1 e.2)
      (slotPortGraph (CompressorRefresh.union (shrinkingGraph P layout n order hc hn good) padding))
      (slotLabels P hn good layout n order hc b pad) :=
  SlotRefinement.balanced (MotifKernel.crossGraph (fun _ : P.Motif => supplyGraph) (partySite P layout))
    (fun e => I e.1 e.2)
    (slotPortGraph (CompressorRefresh.union (shrinkingGraph P layout n order hc hn good) padding))
    (fun e => n (typeIndex P hn good layout e)) b (fun _e => positive _)
    (allPieceSlots P hn good layout n order hc pad) encode (physical_ends P hn good layout n order hc pad padding)

/-- The grouped physical crossing graph has a single-term equality-preserving
history rewrite to the numbered, parallelized, padded slot graph. -/
def subdivision (K : Type) [CommSemiring K]
    (I : P.Motif → Fin 8 → Type) [∀ m e, Fintype (I m e)] [∀ m e, Inhabited (I m e)]
    (b : CrossEdge P layout → ℕ) (encode : ∀ e : CrossEdge P layout, I e.1 e.2 ≃ Fin (2^b e))
    (positive : ∀ t, 0 < n t) (pad : ℕ) (padding : LiftedSlots (V × Tag) pad L) :
    Rewrite (MotifKernel.crossShape (fun _ : P.Motif => supplyGraph) (partySite P layout) I) K := by
  letI (a : Numbered V Tag L (usedDegree n c d+pad)) : Fintype (slotLabels P hn good layout n order hc b pad a) := by
    unfold slotLabels
    infer_instance
  exact (subdivisionRefines P hn good layout n order hc I b encode positive pad padding).rewrite

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
