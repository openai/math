import OAI.ThreeFlat.Diagonal.ShrinkHistoryStep
import OAI.ThreeFlat.Diagonal.ShrinkIntegerLayout
import OAI.ThreeFlat.Diagonal.HistogramPortKernel
import OAI.ThreeFlat.Diagonal.FixedMotifTile

namespace OAI
/-! # A histogram-indexed shrink with numbered balanced target slots

The scored grid search supplies a fixed base tile and its copy count per
actual physical motif. The term consists of one histogram per motif. Its
integer width vector determines the common layout, target slots, and
site-local coefficient maps of one recursive compression step.
-/

namespace ThreeFlat.Diagonal.CompressorPacking

open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression HistoryContraction MotifOuterTerms
open scoped Classical BigOperators
noncomputable section

variable {c d Q : ℕ} {V H Tag L F : Type}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] [CommSemiring F]
variable (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c → ℕ)
  (code : Arc V H Tag L d c ↪ ℕ) (hQ : 0<Q)
  (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q) (bundled : ∀ m, (num m).1 = P.bundle m)
  (base : P.Motif → Fin 2 → ℕ) (r : P.Motif → ℕ)
  (T : ∀ m, FixedMotifTile demandGraph supplyGraph (base m) F)
  (fits : ∀ m e, demandWidth P w num m e ≤ base m e*r m)

abbrev Histories := ∀ m : P.Motif, Histogram (T m).Alphabet (r m)

/-- Combined wire length, including the fixed-width code for each base selector. -/
def historyWidth (x : Histories P base r T) (m : P.Motif) (e : Fin 8) :=
  histWidth (T m).output (x m) e + r m * (T m).bits

/-- Choose the same less expensive placement at every motif. -/
def historyLayout (x : Histories P base r T) := ShrinkMotif.chooseWidths (historyWidth P base r T x)

private abbrev alphabet (m : P.Motif) (s : Histogram (T m).Alphabet (r m)) (e : Fin 8) :=
  (Fin (r m) → Fin (2^(T m).bits)) × Fin (2^histWidth (T m).output s e)

/-- The physical history step, with the labelled target permutation including
all required padding and an explicit readout for every surviving payload. -/
def histogramStep {count : ℕ} (enum : Fin count ≃ Histories P base r T)
    (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset)
    (n : Fin 4 → ℕ) (positive : ∀ i, 0<n i) (order : ShrinkEdge P n ↪ ℕ) (hc : 2≤c)
    (pad : ℕ) (padding : LiftedSlots (V×Tag) pad L) : Rewrite (oldShape P w) F := by
  let I := alphabet P base r T
  let eval (m : P.Motif) := histogramKernel demandGraph ShrinkMotif.supply (demandWidth P w num m)
    (base m) (fits m) (T m).output (T m).encode (T m).entry
  let R := shrinkingStep P w code hQ num bundled (fun m => Histogram (T m).Alphabet (r m)) I eval
    (fun m => histogram_port_kernel demandGraph ShrinkMotif.supply (demandWidth P w num m) (base m)
      (fits m) (T m).output (T m).encode (T m).entry (T m).identity)
    (historyLayout P base r T) enum
  let out (h : Fin count) := historyLayout P base r T (enum h)
  let width (h : Fin count) (e : CrossEdge P (out h)) := historyWidth P base r T (enum h) e.1 e.2
  let graph (h : Fin count) := slotPortGraph (CompressorRefresh.union (shrinkingGraph P (out h) n order hc hn good) padding)
  let labels (h : Fin count) := slotLabels P hn good (out h) n order hc (width h) pad
  refine @SlotRefinement.refineTargets F _ _ R (fun _ => Numbered V Tag L (usedDegree n c d + pad))
    (fun _ => inferInstance) graph labels (fun h e => ?_) ?_
  · unfold labels slotLabels
    exact Fin.fintype _
  intro h
  exact subdivisionRefines P hn good (out h) n order hc (fun m => I m (enum h m)) (width h)
    (fun e => SlotRefinement.selectorWord (r e.1) (T e.1).bits (histWidth (T e.1).output (enum h e.1) e.2)) positive pad padding

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
