import OAI.ThreeFlat.Diagonal.HistoryPhysicalStages
import OAI.ThreeFlat.Diagonal.PhysicalWordAssembly

namespace OAI
/-! # The installed source chart preserves the selected shrink stage's work -/

namespace ThreeFlat.Diagonal.HistoryRelabel
open LinearAlgebra.SpectralBooks HistoryContraction
open scoped Classical BigOperators

variable {U E V H Pins F : Type} [Fintype U] [Fintype E] [Fintype V] [Fintype H] [Field F]
  {G : PortGraph U E} {B : PortGraph V H} {w : E → ℕ} {b : H → ℕ}
  (I : Iso (WordLayout.shape G w) (WordLayout.shape B b)) (L : WordLayout G w Pins)
  {R : Rewrite (WordLayout.shape B b) F} {idx : Fin R.count} {next : Form (R.target idx) Pins}

theorem Iso.onStage_freshResources (stage : Stage R idx (I.pushWord L).ports.form next)
    (width : ∀ e,w e=b (I.edge e)) (bits : ∀ e z,(I.label e z).val=z.val) (v : (R.target idx).Site) :
    (I.onStage L stage width bits).freshResources v = stage.freshResources v := rfl

end ThreeFlat.Diagonal.HistoryRelabel

namespace ThreeFlat.Diagonal.CompressorPacking
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression HistoryContraction MotifKernel MotifOuterTerms
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 260000
set_option maxRecDepth 8000
set_option quotPrecheck false

variable {c d Q : ℕ} {V H Tag L F Pins : Type} [Field F] [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c → ℕ)
    (code : Arc V H Tag L d c ↪ ℕ) (hQ : 0<Q) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q) (bundled : ∀ m, (num m).1=P.bundle m)
    (base : P.Motif → Fin 2 → ℕ) (r : P.Motif → ℕ) (T : ∀ m, FixedMotifTile demandGraph supplyGraph (base m) F)
    (fits : ∀ m e, demandWidth P w num m e ≤ base m e*r m) {terms : ℕ} (hist : Fin terms ≃ Histories P base r T)
    (hn : ∀ a : Tag, -a=a) (good : TagConditions P.slots (shift P) P.offset) (n : Fin 4 → ℕ)
    (positive : ∀ i, 0<n i) (order : ShrinkEdge P n ↪ ℕ) (hc : 2≤c) (pad : ℕ) (padding : LiftedSlots (V×Tag) pad L)
    (idx : Fin terms)

variable {U E : Type} [Fintype U] [Fintype E] {source : PortGraph U E} {width : E → ℕ}
    (I : HistoryRelabel.Iso (WordLayout.shape source width) (WordLayout.shape (oldGraph P) w))
    (layout : WordLayout source width Pins)
    (edgeWidth : ∀ e,width e=w (I.edge e)) (keep : ∀ e z,(I.label e z).val=z.val)
variable (counts : Site V Tag L → ℕ) (ord : ∀ v, Fin (counts v) ≃ {i // P.placement (historyLayout P base r T (hist idx)) i=v})
    (sites : Site V Tag L → ℕ) (motifs : ∀ v, Fin (sites v) ≃ Active (partySite P (historyLayout P base r T (hist idx))) v)

local notation "metricStep" => histogramStep P w code hQ num bundled base r T fits hist hn good n positive order hc pad padding
local notation "lay" => historyLayout P base r T (hist idx)
local notation "packed" => I.pushWord (G:=source) (H:=oldGraph P) (w:=width) (b:=w) layout
local notation "raw" => shrinkAssembly P w code hQ num bundled base r T fits hist hn good n positive order hc pad padding idx packed counts ord sites motifs
local notation "fresh" => shrinkWordLayout (Pins:=Pins) P base r T hist hn good n order hc pad padding idx

/-- The native stage installed in the numbered graph has the same paid local
tree as the elected shrink kernel on its packed original half words. -/
theorem shrink_fresh_on_chart (v : Site V Tag L) (C u D : ℕ)
    (tiles : ∀ m : Active (partySite P lay) v, shrinkTariff P base T m.val ≤ C)
    (heights : ∀ m : Active (partySite P lay) v, HistogramTileNetwork.siteHeight (r m.val) (T m.val).bitCap ≤ u)
    (bounded : sites v ≤ D) :
    (I.onStage (G:=source) (H:=oldGraph P) (w:=width) (b:=w) (R:=metricStep) (idx:=idx)
      layout raw edgeWidth keep).freshResources v ≤
      (2+(1+D+2*C*(D+1)))*(u+1)^3*
        (1+((packed).ports.hidden (R:=metricStep) (t:=idx) counts ord v+(fresh).ports.halfBits v)+
          ∑ m : Active (partySite P lay) v,r m.val) :=
  (I.onStage_freshResources layout raw edgeWidth keep v).le.trans
    (shrink_fresh_uniform P w code hQ num bundled base r T fits hist hn good n positive order hc pad padding idx
      packed counts ord sites motifs v C u D tiles heights bounded)

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
