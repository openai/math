import OAI.ThreeFlat.Diagonal.HistoryPortFootprint
import OAI.ThreeFlat.Diagonal.ShrinkSiteTree
import OAI.ThreeFlat.Diagonal.RefreshSiteTree

namespace OAI
/-! # Replay depth of the physical shrink and refresh site trees -/

namespace ThreeFlat.Diagonal

open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression HistoryContraction MotifOuterTerms MotifKernel MotifBinaryPacking HistogramTileNetwork
open scoped Classical BigOperators
noncomputable section



namespace CompressorPacking

set_option maxHeartbeats 1000000
set_option maxRecDepth 16000

attribute [local irreducible] historyLayout shrinkingGraph slotPortGraph
  SlotRefinement.actualWidth allPieceSlots

open private sitePins pieceAt from OAI.ThreeFlat.Diagonal.ShrinkSiteTree

variable {c d Q p : ℕ} {V H Tag L F : Type} [Field F] [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c → ℕ)
    (code : Arc V H Tag L d c ↪ ℕ) (hQ : 0<Q) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q)
    (base : P.Motif → Fin 2 → ℕ) (r : P.Motif → ℕ) (T : ∀ m, FixedMotifTile demandGraph supplyGraph (base m) F)
    (fit : ∀ m e, demandWidth P w num m e ≤ base m e*r m) (x : Histories P base r T)
    (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset)
    (n : Fin 4 → ℕ) (positive : ∀ i, 0<n i) (order : ShrinkEdge P n ↪ ℕ) (hc : 2≤c) (pad : ℕ)
    (padding : LiftedSlots (V×Tag) pad L) (v : Site V Tag L)

local notation "layout" => historyLayout P base r T x
variable (old : (i : {i // P.placement (historyLayout P base r T x) i=v}) → (a : (oldGraph P).Port i.val) → Fin (w a.1.1) → Fin p)
    (new : sitePins (outGraph P hn good (historyLayout P base r T x) n order hc pad padding) (outputWidth P base r T x hn good (historyLayout P base r T x) n order hc pad) v p)

/-- The active-motif join and the occupied-party join add two levels above a party. -/
theorem shrinkSite_within {s : ℕ} (enum : Fin s ≃ Active (partySite P layout) v) :
    Tree.Within 4 (shrinkSite (p:=p) P w code hQ num base r T x hn good n positive order
      hc pad padding v old new enum) := by
  unfold shrinkSite Tree.activeTree
  apply Tree.Within.join
  intro i
  let := (T (enum i).val).hasLetter
  unfold shrinkPiece pieceAt Tree.occupiedTree
  apply Tree.Within.join
  intro j
  apply Tree.party_within


end CompressorPacking
end
end ThreeFlat.Diagonal
namespace ThreeFlat.Diagonal.RefreshTies

set_option maxHeartbeats 1000000
set_option maxRecDepth 16000

open Computability.VPVNP.Compression Computability.VPVNP.MotifSelector LinearAlgebra.SpectralBooks Expander HistoryContraction MotifOuterTerms HistogramTileNetwork
open scoped Classical BigOperators
noncomputable section

variable {V C L F : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L] [Field F]
  {m h p : ℕ} (G : LiftedSlots V m (C×L)) (port : Fin m ≃ C) (c : Fin m → Fin m → ℕ)
  (w : Address (V×L) m → ℕ) (base : V×L → Bool×Fin m×Fin m → ℕ) (r : V×L → ℕ)
  (T : ∀ u, FixedMotifTile (RefreshMotif.denseGraph m) (ports c) (base u) F) (x : Histories c base r T)
  (hm : 2 ≤ m) (hh : 0<h) (pad : ℕ) (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h)
  (zero : ∀ i, c i i=0) {γ : ℝ} (bound : Bound (transition c h) ℝ γ) (u : V×L) (v : Fin m)

open private outputPins from OAI.ThreeFlat.Diagonal.RefreshSiteTree

variable (old : (a : (oldPortGraph (arrival G port)).Port (u,v)) → Fin (w a.1.1) → Fin p)
  (new : outputPins G c hm pad sym rows zero (termWidth c w (sparseWidth c base r T x)) (u,v) p)

attribute [local irreducible] actualPortGraph freshWidth

omit [Fintype V] [Fintype L] in
/-- A refresh site joins one party tree, so its replay has at most three levels. -/
theorem siteTree_within :
    Tree.Within 3 (siteTree (p:=p) G port c w base r T x hm hh pad sym rows zero bound u v old new) := by
  let : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
  let := (T u).hasLetter
  unfold siteTree Tree.directParty
  apply Tree.Within.join
  intro i
  apply Tree.party_within


end
end ThreeFlat.Diagonal.RefreshTies

end OAI
