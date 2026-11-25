import OAI.ThreeFlat.Diagonal.HistoryMaskOrder
import OAI.ThreeFlat.Diagonal.FixedTileCapacity
import OAI.ThreeFlat.Diagonal.HistoryOccupiedTrees
import OAI.ThreeFlat.Diagonal.ShrinkHistoryWires
import OAI.ThreeFlat.Diagonal.ShrinkActiveSites
import OAI.ThreeFlat.Diagonal.HistogramPartyBudget

namespace OAI
/-! # Actual compact-site tree for one physical shrink

The inherited half-words and the regularized, numbered successor slots are
both read in physical bit coordinates. Unoccupied motifs are dropped before
constructing any local network. All sorter leaves are cropped instances of
the fixed dyadic sort template, and every other leaf is a bounded base LUT.
-/

namespace ThreeFlat.Diagonal

open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression HistoryContraction MotifOuterTerms MotifKernel MotifBinaryPacking HistogramTileNetwork
open scoped Classical BigOperators
noncomputable section



namespace CompressorPacking

set_option maxHeartbeats 450000
set_option maxRecDepth 16000

-- The layout decision is an input to every local wire and need not reduce here.
attribute [local irreducible] historyLayout shrinkingGraph slotPortGraph
  SlotRefinement.actualWidth allPieceSlots

variable {c d Q p : ℕ} {V H Tag L F : Type} [Field F] [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c → ℕ)
    (code : Arc V H Tag L d c ↪ ℕ) (hQ : 0<Q) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q)
    (base : P.Motif → Fin 2 → ℕ) (r : P.Motif → ℕ) (T : ∀ m, FixedMotifTile demandGraph supplyGraph (base m) F)
    (fit : ∀ m e, demandWidth P w num m e ≤ base m e*r m) (x : Histories P base r T)
    (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset)
    (n : Fin 4 → ℕ) (positive : ∀ i, 0<n i) (order : ShrinkEdge P n ↪ ℕ) (hc : 2≤c) (pad : ℕ)
    (padding : LiftedSlots (V×Tag) pad L) (v : Site V Tag L)

private abbrev sitePins {A B : Type} (g : PortGraph A B) (width : B → ℕ) (site : A) (count : ℕ) :=
  (a : g.Port site) → Fin (width a.val.1) → Fin count

private abbrev sitePinsRead {A B : Type} (g : PortGraph A B) (width : B → ℕ) (site : A) {count : ℕ}
    (pins : sitePins g width site count) (pin : Fin count → Bool) (words : g.State (fun e => Fin (2^width e)) site) :=
  ∀ a t, pin (pins a t) = (words a).val.testBit t.val

variable (old : (i : {i // P.placement (historyLayout P base r T x) i=v}) → (a : (oldGraph P).Port i.val) → Fin (w a.1.1) → Fin p)
    (new : sitePins (outGraph P hn good (historyLayout P base r T x) n order hc pad padding) (outputWidth P base r T x hn good (historyLayout P base r T x) n order hc pad) v p)

private abbrev Abs (m : P.Motif) := Absorbed supplyGraph (partySite P (historyLayout P base r T x) m) v
private abbrev Part (m : P.Motif) := {j // partySite P (historyLayout P base r T x) m j = v}
private abbrev ps (m : P.Motif) := HistoryMaskOrder.order (fun j => partySite P (historyLayout P base r T x) m j=v)
private abbrev widthCap (m : P.Motif) := (T m).bitCap
private abbrev level (m : P.Motif) := siteHeight (r m) (T m).bitCap
private abbrev Ctile (m : P.Motif) := MotifNativeCompactors.partialInput F (r m*(T m).bitCap) (level P base r T m)
private abbrev Ccount (m : P.Motif) := MotifNativeCompactors.partialInput F (r m) (level P base r T m)

/-- One present motif at the site. Since there are six parties and eight
supply edges, these four enumerations range over fixed finite families. -/
private def pieceAt (lay : Bool)
    (localPins : (i : {i // P.placement lay i=v}) → (a : (oldGraph P).Port i.val) → Fin (w a.1.1) → Fin p)
    (nextPins : sitePins (outGraph P hn good lay n order hc pad padding)
      (outputWidth P base r T x hn good lay n order hc pad) v p) (m : P.Motif) : Tree F p := by
  letI := (T m).hasLetter
  let ps := HistoryMaskOrder.order (fun j => partySite P lay m j=v)
  let crossed := crossingPin (p:=p) P base r T x hn good lay n positive order hc pad padding v nextPins m
  exact Tree.occupiedTree demandGraph ShrinkMotif.supply (partySite P lay m) v (demandWidth P w num m)
    (base m) (T m).output (T m).encode (Fintype.equivFin _) (x m) (HistoryMaskOrder.order (fun e => wireOwner supplyGraph.tail supplyGraph.head (partySite P lay m) e=some v)) ps
    (fun i => (Fintype.equivFin (supplyGraph.Port (ps i).val)).symm)
    (fun i => (Fintype.equivFin (demandGraph.Port (ps i).val)).symm)
    (fun i a e => (T m).output_le_cap a _) (T m).entry (Ctile P base r T m) (Ccount P base r T m)
    (fun i q t => oldPinSource P w code hQ num lay v localPins m (ps i).val q t)
    crossed

def shrinkPiece :=
  pieceAt (p:=p) P w code hQ num base r T x hn good n positive order hc pad padding v (historyLayout P base r T x)

def shrinkSite {s : ℕ} (enum : Fin s ≃ Active (partySite P (historyLayout P base r T x)) v) : Tree F p :=
  Tree.activeTree (partySite P (historyLayout P base r T x)) v enum (fun m => shrinkPiece P w code hQ num base r T x hn good n positive order hc pad padding v old new m.val)

theorem shrinkPiece_eval (m : P.Motif) (pin : Fin p → Bool) (z : OwnedRow P w (historyLayout P base r T x) v) (ys : ((outGraph P hn good (historyLayout P base r T x) n order hc pad padding)).State (fun e => Fin (2^(outputWidth P base r T x hn good (historyLayout P base r T x) n order hc pad) e)) v)
    (oldRead : ∀ i a t, pin (old i a t) = (word (w a.1.1)).symm (z i a) t) (newRead : sitePinsRead (count:=p) (outGraph P hn good (historyLayout P base r T x) n order hc pad padding) (outputWidth P base r T x hn good (historyLayout P base r T x) n order hc pad) v new pin ys) :
    (shrinkPiece P w code hQ num base r T x hn good n positive order hc pad padding v old new m).compile.eval pin =
      groupedFactor supplyGraph (partySite P (historyLayout P base r T x) m) (fun j => histogramKernel demandGraph ShrinkMotif.supply
        (demandWidth P w num m) (base m) (fit m) (T m).output (T m).encode (T m).entry (x m) j (fun q =>
          demandEnd P code w hQ num m (oldEnds P w (wholeRow P w (historyLayout P base r T x) v z) false) (oldEnds P w (wholeRow P w (historyLayout P base r T x) v z) true) q.1.2 q.1.1)) v
        (visible (fun _ : P.Motif => supplyGraph) (partySite P (historyLayout P base r T x))
          (fun k e => HistogramTileNetwork.Label (x k) (T k).output (T k).bits e) v ((outRead P base r T x hn good (historyLayout P base r T x) n positive order hc pad padding).read v ys) m) := by
  let := (T m).hasLetter
  let ps := HistoryMaskOrder.order (fun j => partySite P (historyLayout P base r T x) m j=v)
  let crossed := crossingPin (p:=p) P base r T x hn good (historyLayout P base r T x) n positive order hc pad padding v new m
  refine (Tree.occupiedTree_eval demandGraph ShrinkMotif.supply (partySite P (historyLayout P base r T x) m) v (demandWidth P w num m)
      (base m) (T m).output (T m).encode (Fintype.equivFin _) (x m) (HistoryMaskOrder.order (fun e => wireOwner supplyGraph.tail supplyGraph.head (partySite P (historyLayout P base r T x) m) e=some v)) ps
      (fun i => (Fintype.equivFin (supplyGraph.Port (ps i).val)).symm)
      (fun i => (Fintype.equivFin (demandGraph.Port (ps i).val)).symm)
      (fun i a e => (T m).output_le_cap a _) (T m).entry (Ctile P base r T m) (Ccount P base r T m)
      (fun i q t => oldPinSource P w code hQ num (historyLayout P base r T x) v old m (ps i).val q t)
      crossed pin).trans ?_
  refine occupied_eval demandGraph ShrinkMotif.supply (partySite P (historyLayout P base r T x) m) v (demandWidth P w num m)
      (base m) (T m).output (T m).encode (Fintype.equivFin _) (x m) (HistoryMaskOrder.order (fun e => wireOwner supplyGraph.tail supplyGraph.head (partySite P (historyLayout P base r T x) m) e=some v)) ps
      (fun i => (Fintype.equivFin (supplyGraph.Port (ps i).val)).symm)
      (fun i => (Fintype.equivFin (demandGraph.Port (ps i).val)).symm)
      (fun i a e => (T m).output_le_cap a _) (T m).entry (Ctile P base r T m) (Ccount P base r T m)
      (fun i q t => oldPinSource P w code hQ num (historyLayout P base r T x) v old m (ps i).val q t)
      crossed (fit m) ?_ ?_ pin
    (fun j q => demandEnd P code w hQ num m (oldEnds P w (wholeRow P w (historyLayout P base r T x) v z) false)
      (oldEnds P w (wholeRow P w (historyLayout P base r T x) v z) true) q.1.2 q.1.1)
    (visible (fun _ : P.Motif => supplyGraph) (partySite P (historyLayout P base r T x))
      (fun k e => HistogramTileNetwork.Label (x k) (T k).output (T k).bits e) v
      ((outRead P base r T x hn good (historyLayout P base r T x) n positive order hc pad padding).read v ys) m) ?_ ?_
  · exact MotifNativeCompactors.partialInput_eval _ _ ((Nat.le_max_right _ _).trans (siteHeight_room _ _))
  · exact MotifNativeCompactors.partialInput_eval _ _ ((Nat.le_max_left _ _).trans (siteHeight_room _ _))
  · intro i q t g
    exact oldPinSource_read P w code hQ num (historyLayout P base r T x) v old g pin z oldRead m _ q t
  · exact crossingPin_read P base r T x hn good (historyLayout P base r T x) n positive order hc pad padding v new pin ys newRead m

/-- Against the actual refined rewrite kernel, including the same physical
half-edge subdivision as `histogramStep`. -/
theorem shrinkSite_eval {s count : ℕ} (enum : Fin s ≃ Active (partySite P (historyLayout P base r T x)) v)
    (hist : Fin count ≃ Histories P base r T) (idx : Fin count) (same : hist idx = x)
    (bundled : ∀ m, (num m).1 = P.bundle m) (pin : Fin p → Bool) (z : OwnedRow P w (historyLayout P base r T x) v)
    (ys : ((outGraph P hn good (historyLayout P base r T x) n order hc pad padding)).State (fun e => Fin (2^(outputWidth P base r T x hn good (historyLayout P base r T x) n order hc pad) e)) v)
    (oldRead : ∀ i a t, pin (old i a t) = (word (w a.1.1)).symm (z i a) t) (newRead : sitePinsRead (count:=p) (outGraph P hn good (historyLayout P base r T x) n order hc pad padding) (outputWidth P base r T x hn good (historyLayout P base r T x) n order hc pad) v new pin ys) :
    (shrinkSite P w code hQ num base r T x hn good n positive order hc pad padding v old new enum).compile.eval pin =
      (histogramStep P w code hQ num bundled base r T fit hist hn good n positive order hc pad padding).kernel idx v
        (Eq.mp (congrArg (fun h => OwnedRow P w (historyLayout P base r T h) v) same.symm) z)
        (Eq.mp (congrArg (fun h => (outGraph P hn good (historyLayout P base r T h) n order hc pad padding).State
          (fun e => Fin (2^(outputWidth P base r T h hn good (historyLayout P base r T h) n order hc pad e))) v)
          same.symm) ys) := by
  subst x
  let lay := historyLayout P base r T (hist idx)
  let : ∀ i, Inhabited ((oldShape P w).Half i) :=
    fun _ => ⟨fun e => (⟨0,Nat.two_pow_pos _⟩ : Fin (2^w e.val.1))⟩
  have full : extendRow (oldShape P w).Half (P.placement lay) v z = wholeRow P w lay v z := by
    funext i a
    by_cases localSite : P.placement lay i = v <;> simp [extendRow,wholeRow,localSite] <;> rfl
  let child (m : Active (partySite P lay) v) := shrinkPiece P w code hQ num base r T (hist idx)
    hn good n positive order hc pad padding v old new m.val
  let K (m : P.Motif) (j : Fin 6) :=
    histogramKernel demandGraph ShrinkMotif.supply (demandWidth P w num m) (base m) (fit m)
      (T m).output (T m).encode (T m).entry (hist idx m) j (fun q =>
        demandEnd P code w hQ num m (oldEnds P w (wholeRow P w lay v z) false)
          (oldEnds P w (wholeRow P w lay v z) true) q.1.2 q.1.1)
  let wires (m : P.Motif) := visible (fun _ : P.Motif => supplyGraph) (partySite P lay)
    (fun k e => HistogramTileNetwork.Label (hist idx k) (T k).output (T k).bits e) v
    ((outRead P base r T (hist idx) hn good lay n positive order hc pad padding).read v ys) m
  have evaluated := Tree.activeTree_eval (fun _ : P.Motif => supplyGraph) (partySite P lay) v enum
    child K wires pin (fun m => shrinkPiece_eval P w code hQ num base r T fit (hist idx)
      hn good n positive order hc pad padding v old new m.val pin z ys oldRead newRead)
  refine evaluated.trans ?_
  simp only [histogramStep,SlotRefinement.refineTargets,shrinkingStep,historyStep,stepKernel]
  dsimp only [K]
  rw [←full]; rfl


end CompressorPacking
end
end ThreeFlat.Diagonal

end OAI
