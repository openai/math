import OAI.ThreeFlat.Diagonal.ShrinkSiteTree
import OAI.ThreeFlat.Diagonal.HistoryWordLayout
import OAI.ThreeFlat.Diagonal.CompressorHalfOrder

namespace OAI
/-! # A full ordered assembler at the genuine physical shrink step -/
namespace ThreeFlat.Diagonal.CompressorPacking

open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression HistoryContraction MotifKernel MotifOuterTerms
open scoped Classical BigOperators
noncomputable section

variable {c d Q : ℕ} {V H Tag L F Pins : Type} [Field F] [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c → ℕ)
    (code : Arc V H Tag L d c ↪ ℕ) (hQ : 0<Q) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q) (bundled : ∀ m, (num m).1=P.bundle m)
    (base : P.Motif → Fin 2 → ℕ) (r : P.Motif → ℕ) (T : ∀ m, FixedMotifTile demandGraph supplyGraph (base m) F)
    (fits : ∀ m e, demandWidth P w num m e ≤ base m e*r m) {terms : ℕ} (hist : Fin terms ≃ Histories P base r T)
    (hn : ∀ a : Tag, -a=a) (good : TagConditions P.slots (shift P) P.offset) (n : Fin 4 → ℕ)
    (positive : ∀ i, 0<n i) (order : ShrinkEdge P n ↪ ℕ) (hc : 2≤c) (pad : ℕ) (padding : LiftedSlots (V×Tag) pad L)
    (idx : Fin terms) (A : WordLayout (oldGraph P) w Pins)

/-- The next incident half-ports use exactly the outgoing bank followed by
its inverse-permutation incoming bank. External pins are attached by the
actual child order in `shrinkAssembly`. -/
def shrinkWordLayout : WordLayout
    (outGraph P hn good (historyLayout P base r T (hist idx)) n order hc pad padding)
    (outputWidth P base r T (hist idx) hn good (historyLayout P base r T (hist idx)) n order hc pad) Pins where
  count _ := 2*(usedDegree n c d+pad)
  order v := HalfOrder.order (CompressorRefresh.union
    (shrinkingGraph P (historyLayout P base r T (hist idx)) n order hc hn good) padding) v
  ext _ := 0
  pin _ _ := Fin.elim0

variable (counts : Site V Tag L → ℕ) (ord : ∀ v, Fin (counts v) ≃ {i // P.placement (historyLayout P base r T (hist idx)) i=v})
    (sites : Site V Tag L → ℕ) (motifs : ∀ v, Fin (sites v) ≃ Active (partySite P (historyLayout P base r T (hist idx))) v)

/-- Complete finite-stage realization, independent of the inherited seed
networks. The only ordering inputs enumerate actual children and actual
active motifs seen by the native compact navigation rows. -/
def shrinkAssembly : Stage
    (histogramStep P w code hQ num bundled base r T fits hist hn good n positive order hc pad padding)
    idx A.ports.form (A.ports.inherit
      (R := histogramStep P w code hQ num bundled base r T fits hist hn good n positive order hc pad padding)
      (t := idx) (shrinkWordLayout (Pins:=Pins) P base r T hist hn good n order hc pad padding idx).ports counts ord).form := by
  let step := histogramStep P w code hQ num bundled base r T fits hist hn good n positive order hc pad padding
  let words := shrinkWordLayout (Pins:=Pins) P base r T hist hn good n order hc pad padding idx
  apply A.ports.wordsStage (R:=step) (t:=idx) words.ports counts ord
    (fun v => shrinkSite P w code hQ num base r T (hist idx) hn good n positive order hc pad padding v
      (A.ports.stageOld (R:=step) (t:=idx) words.ports counts ord v) (A.ports.stageNew (R:=step) (t:=idx) words.ports counts ord v) (motifs v))
  intro v pin x y ox oy
  exact shrinkSite_eval P w code hQ num base r T fits (hist idx) hn good n positive order hc pad padding v _ _
    (motifs v) hist idx rfl bundled pin x y ox oy

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
