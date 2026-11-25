import OAI.ThreeFlat.Diagonal.HistorySiteDepth
import OAI.ThreeFlat.Diagonal.PhysicalRefreshInputStage

namespace OAI
/-! # Tree depth at each site of an installed refresh table -/

namespace ThreeFlat.Diagonal.HistoryContraction

/-- Changing the destination form keeps the tree at every site. -/
theorem Stage.reform_within {F P : Type*} [CommSemiring F] {S : Shape} {R : Rewrite S F}
    {i : Fin R.count} {src : Form S P} {a b : Form (R.target i) P}
    (stage : Stage R i src a) (same : a=b) (k : ℕ) (z : (R.target i).Site)
    (size : Tree.Within k (stage.root z)) : Tree.Within k ((stage.reform same).root z) := size

end ThreeFlat.Diagonal.HistoryContraction

namespace ThreeFlat.Diagonal.RefreshTies
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression Expander HistoryContraction
open scoped Classical BigOperators
noncomputable section

variable {V C L F Pins : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L] [Field F]
  {m h : ℕ} (G : LiftedSlots V m (C×L)) (port : Fin m ≃ C) (c : Fin m → Fin m → ℕ)
  (w : Address (V×L) m → ℕ) (base : V×L → Bool×Fin m×Fin m → ℕ) (r : V×L → ℕ)
  (T : ∀ u, FixedMotifTile (RefreshMotif.denseGraph m) (ports c) (base u) F)
  (fit : ∀ u e, profile G port w u e ≤ base u e*r u) (hm : 2 ≤ m) (hh : 0<h) (pad : ℕ)
  (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h) (zero : ∀ i, c i i=0)
  {γ : ℝ} (bound : Bound (transition c h) ℝ γ) (idx : Fin (Fintype.card (Histories c base r T)))

local notation "histStep" => histogramStep G port c w base r T fit hm hh pad sym rows zero bound
local notation "actualGraph" => actualPortGraph (outputGraph G c sym rows zero hm pad)
set_option quotPrecheck false in
local notation "chosen" => (Fintype.equivFin (Histories c base r T)).symm idx
local notation "selectedWidth" => freshWidth c rows (termWidth c w (sparseWidth c base r T chosen)) pad

attribute [local irreducible] actualPortGraph freshWidth
set_option maxRecDepth 6000
set_option maxHeartbeats 280000

theorem refresh_root_within_at_width (old : WordLayout (oldPortGraph (arrival G port)) w Pins)
    (bits : LiveSlot V L m (1+h+pad) → ℕ)
    (fresh : WordLayout (actualPortGraph (outputGraph G c sym rows zero hm pad)) bits Pins)
    (same : (histStep).target idx=WordLayout.shape actualGraph bits) (j : (V×L)×Fin m) :
    Tree.Within 3 ((refreshAssemblyAtWidth G port c w base r T fit hm hh pad sym rows zero bound
      idx old bits fresh same).root j) := by
  have widths : selectedWidth=bits := WordLayout.width_injective actualGraph same
  subst bits
  let out := WordLayout.atWidth selectedWidth fresh
  let child := old.ports.stageOld (R:=histStep) (t:=idx) out.ports (fun _ => 1) singleChild j ⟨j,rfl⟩
  let dest := old.ports.stageNew (R:=histStep) (t:=idx) out.ports (fun _ => 1) singleChild j
  exact siteTree_within G port c w base r T chosen hm hh pad sym rows zero bound j.1 j.2 child dest

end
end ThreeFlat.Diagonal.RefreshTies

namespace ThreeFlat.Diagonal.RefreshMotif.Table
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression Expander HistoryContraction RefreshTies
open scoped Classical BigOperators
noncomputable section

variable {V C L F Pins U E : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L]
  [Field F] [Fintype U] [Fintype E] {m h pad : ℕ} {c : Fin m → Fin m → ℕ} {tariff γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) tariff) (G : LiftedSlots V m (C×L))
  (port : Fin m ≃ C) (w : Address (V×L) m → ℕ) (hm : 2 ≤ m) (hh : 0<h)
  (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h) (zero : ∀ i,c i i=0)
  (conn : Bound (transition c h) ℝ γ)
  {source : PortGraph U E} {width : E → ℕ}

local notation "rule" => step T G port w hm hh sym rows zero conn
local notation "oldGraph" => oldPortGraph (arrival G port)
local notation "outGraph" => actualPortGraph (outputGraph G c sym rows zero hm pad)
attribute [local irreducible] actualPortGraph freshWidth
set_option maxHeartbeats 400000
set_option maxRecDepth 2600

variable (I : HistoryRelabel.Iso (WordLayout.shape source width) (WordLayout.shape (oldPortGraph (arrival G port)) w))
  (layout : WordLayout source width Pins) (i : Fin (T.step G port w hm hh sym rows zero conn).count)
  (bits : LiveSlot V L m (1+h+pad) → ℕ) (fresh : WordLayout (actualPortGraph (outputGraph G c sym rows zero hm pad)) bits Pins)
  (same : (T.step G port w hm hh sym rows zero conn).target i=WordLayout.shape (actualPortGraph (outputGraph G c sym rows zero hm pad)) bits)
  (edgeWidth : ∀ e,width e=w (I.edge e)) (keep : ∀ e x,(I.label e x).val=x.val)

local notation "installed" => wordStageOnChart T G port w hm hh sym rows zero conn I layout i bits fresh same edgeWidth keep


local notation "packed" => I.pushWord (G:=source) (H:=oldGraph) (w:=width) (b:=w) layout
theorem wordStageOnChart_within (z : (V×L)×Fin m) :
    Tree.Within 3 ((installed).root z) :=
  refresh_root_within_at_width G port c w (fun v => T.base (T.winner G port w v))
    (T.repeats G port w) (T.entry G port w) (fun _v => T.fits _) hm hh pad sym rows zero conn i packed bits fresh same z

end
end ThreeFlat.Diagonal.RefreshMotif.Table

namespace ThreeFlat.Diagonal.PhysicalStage
open LinearAlgebra.SpectralBooks Expander Computability.VPVNP.Compression CompressorPacking HistoryContraction RefreshTies
open scoped Classical BigOperators
noncomputable section

variable {F Pins : Type} [Field F] {m lanes hbits rem h pad : ℕ} {c : Fin m→Fin m→ℕ} {C γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) C) (A : State m lanes)
  (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
  (hm : 2 ≤ m) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (zero : ∀ i,c i i=0) (conn : Bound (transition c h) ℝ γ)

local notation "src" => changeLanes A.graph u
local notation "inputWidth" => refreshInput A u port
local notation "outGraph" => actualPortGraph (outputGraph src c sym rows zero hm pad)
local notation "oldGraph" => oldPortGraph (arrival src port)
local notation "inIso" => StageAddress.refreshInputIso A.graph A.chart u port A.width
local notation "rule" => T.step src port inputWidth hm hh sym rows zero conn
set_option quotPrecheck false

open private edgeAt labelAt from OAI.ThreeFlat.Diagonal.PhysicalRefreshInputStage

variable (L : A.Words Pins) (idx : Fin (T.step (changeLanes A.graph u) port (refreshInput A u port) hm hh sym rows zero conn).count)
  (bits : LiveSlot A.Base (BitWord rem) m (1+h+pad) → ℕ)
  (fresh : WordLayout (actualPortGraph (outputGraph (changeLanes A.graph u) c sym rows zero hm pad)) bits Pins)
  (shapeEq : (T.step (changeLanes A.graph u) port (refreshInput A u port) hm hh sym rows zero conn).target idx =
    WordLayout.shape (actualPortGraph (outputGraph (changeLanes A.graph u) c sym rows zero hm pad)) bits)
  (output : WordLayout (actualPortGraph (outputGraph (changeLanes A.graph u) c sym rows zero hm pad)) bits Pins)

variable (wordsEq : ((StageAddress.refreshInputIso A.graph A.chart u port A.width).pushWord
    (H:=oldPortGraph (arrival (changeLanes A.graph u) port)) (b:=refreshInput A u port) L).inherited
    fresh id (fun _=>1) singleChild = output)

attribute [local irreducible] RefreshMotif.Table.wordStageOnChart

local notation "assembled" => refreshInputStage T A u port hm hh sym rows zero conn L idx bits fresh shapeEq output wordsEq

theorem refreshInputStage_within (z : (A.Base × BitWord rem) × Fin m) :
    Tree.Within 3 ((assembled).root z) :=
  T.wordStageOnChart_within src port inputWidth hm hh sym rows zero conn
    (source:=A.shape.graph) (width:=A.width) (inIso) L idx bits fresh shapeEq (edgeAt A u port) (labelAt A u port) z

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
