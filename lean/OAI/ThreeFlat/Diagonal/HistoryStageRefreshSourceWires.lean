import OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage
import OAI.ThreeFlat.RAM.HistoryStageChartAddresses

namespace OAI
/-! # Numerical wires of the selected refresh before physical installation -/

namespace ThreeFlat.Diagonal.RefreshTies
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression Expander HistoryContraction
open RAM.HistoryStageShapeWires
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

private theorem refresh_raw_wires (old : WordLayout (oldPortGraph (arrival G port)) w Pins)
    (fresh : WordLayout actualGraph selectedWidth Pins) (z : (V×L)×Fin m) :
    At old.ports (refreshAssembly G port c w base r T fit hm hh pad sym rows zero bound idx old fresh)
      z ((old.inherited fresh id (fun _=>1) singleChild).ext z) := by
  unfold refreshAssembly
  apply wordsStage_at (R:=histStep) (t:=idx) old.ports fresh.ports (fun _=>1) singleChild

theorem refresh_wires_at_width (old : WordLayout (oldPortGraph (arrival G port)) w Pins)
    (bits : LiveSlot V L m (1+h+pad) → ℕ) (fresh : WordLayout actualGraph bits Pins)
    (same : (histStep).target idx=WordLayout.shape actualGraph bits) (z : (V×L)×Fin m) :
    At old.ports (refreshAssemblyAtWidth G port c w base r T fit hm hh pad sym rows zero bound idx old bits fresh same)
      z ((old.inherited fresh id (fun _=>1) singleChild).ext z) :=
  (refresh_raw_wires G port c w base r T fit hm hh pad sym rows zero bound idx old
    (WordLayout.atWidth selectedWidth fresh) z).reform
    (WordLayout.inheritedWidth_eq (graph:=actualGraph) (first:=selectedWidth) (second:=bits)
      old same fresh id (fun _=>1) singleChild).symm

end
end ThreeFlat.Diagonal.RefreshTies

namespace ThreeFlat.Diagonal.RefreshMotif.Table
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression Expander HistoryContraction RefreshTies
open RAM.HistoryStageShapeWires
open scoped Classical BigOperators
noncomputable section

variable {V C L F Pins U E : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L]
  [Field F] [Fintype U] [Fintype E] {m h pad : ℕ} {c : Fin m → Fin m → ℕ} {tariff γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) tariff) (G : LiftedSlots V m (C×L))
  (port : Fin m ≃ C) (w : Address (V×L) m → ℕ) (hm : 2 ≤ m) (hh : 0<h)
  (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h) (zero : ∀ i,c i i=0)
  (conn : Bound (transition c h) ℝ γ)
  {source : PortGraph U E} {width : E → ℕ}

set_option quotPrecheck false
local notation "rule" => step T G port w hm hh sym rows zero conn
local notation "oldGraph" => oldPortGraph (arrival G port)

variable (I : HistoryRelabel.Iso (WordLayout.shape source width) (WordLayout.shape (oldPortGraph (arrival G port)) w))
  (layout : WordLayout source width Pins) (i : Fin (T.step G port w hm hh sym rows zero conn).count)
  (bits : LiveSlot V L m (1+h+pad) → ℕ)
  (fresh : WordLayout (actualPortGraph (outputGraph G c sym rows zero hm pad)) bits Pins)
  (same : (T.step G port w hm hh sym rows zero conn).target i =
    WordLayout.shape (actualPortGraph (outputGraph G c sym rows zero hm pad)) bits)
  (edgeWidth : ∀ e,width e=w (I.edge e)) (keep : ∀ e x,(I.label e x).val=x.val)

local notation "packed" => I.pushWord (G:=source) (H:=oldGraph) (w:=width) (b:=w) layout
local notation "base" => (fun a => T.base (T.winner G port w a))
local notation "copies" => T.repeats G port w
local notation "tile" => T.entry G port w

attribute [local irreducible] actualPortGraph freshWidth refreshAssemblyAtWidth
set_option maxRecDepth 2600 in
set_option maxHeartbeats 400000 in
/-- The selected refresh row keeps its numerical wiring on the numbered source chart. -/
theorem wordStageOnChart_wires (z : (V×L)×Fin m) :
    At layout.ports (wordStageOnChart T G port w hm hh sym rows zero conn I layout i bits fresh same edgeWidth keep)
      z (((I.pushWord (G:=source) (H:=oldPortGraph (arrival G port)) (w:=width) (b:=w) layout).inherited
        fresh id (fun _=>1) singleChild).ext z) := by
  let s := refreshAssemblyAtWidth G port c w base copies tile (fun v=>T.fits _)
    hm hh pad sym rows zero conn i packed bits fresh same
  have wires := RefreshTies.refresh_wires_at_width G port c w base copies tile (fun v=>T.fits _)
    hm hh pad sym rows zero conn i packed bits fresh same z
  exact At.onStage (G:=source) (H:=oldGraph) (w:=width) (b:=w) (I:=I) (L:=layout)
    (R:=rule) (t:=i) (s:=s) (hw:=edgeWidth) (hv:=keep) (v:=z)
    (external:=((packed).inherited fresh id (fun _=>1) singleChild).ext z) wires

end
end ThreeFlat.Diagonal.RefreshMotif.Table


namespace ThreeFlat.Diagonal.PhysicalStage
open LinearAlgebra.SpectralBooks Expander Computability.VPVNP.Compression CompressorPacking HistoryContraction RefreshTies
open RAM.HistoryStageShapeWires
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

private theorem input_wires (z : (A.Base × BitWord rem) × Fin m) :
    At L.ports (refreshInputStage T A u port hm hh sym rows zero conn L idx bits fresh shapeEq output wordsEq)
      z (output.ext z) := by
  let read := T.wordStageOnChart_wires src port inputWidth hm hh sym rows zero conn
    (source:=A.shape.graph) (width:=A.width) (inIso) L idx bits fresh shapeEq (edgeAt A u port) (labelAt A u port) z
  have same := congrArg (fun a : WordLayout outGraph bits Pins => a.ext z) wordsEq
  refine same ▸ ?_
  exact read.reform (congrArg (fun w : WordLayout outGraph bits Pins =>
    (shapeEq.symm ▸ w.ports.form : Form ((rule).target idx) Pins)) wordsEq)

end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage
open LinearAlgebra.SpectralBooks Expander Computability.VPVNP.Compression CompressorPacking HistoryContraction RefreshTies
open RAM.HistoryStageShapeWires
open scoped Classical BigOperators
noncomputable section

variable {F Pins : Type} [Field F] {m lanes hbits rem h pad : ℕ} {c : Fin m→Fin m→ℕ} {C γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) C) (A : State m lanes)
  (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
  (hm : 2 ≤ m) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (zero : ∀ i,c i i=0) (conn : Bound (transition c h) ℝ γ)
  (L : A.Words Pins) (idx : Fin (refreshMove T A u port hm hh sym rows zero conn).rules.count)

attribute [local irreducible] CompressorRefresh.graph RefreshTies.freshWidth
  RefreshMotif.Table.wordStageOnChart RefreshTies.refreshAssemblyAtWidth

open private selectedBits outputWords outputShape selectedOutput issuedWords
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- The input chart and both changes of destination form retain the numerical
kernel and child maps of the selected table's one-child assembly. -/
theorem RefreshPrepared.source_wires (z : (A.Base × BitWord rem) × Fin m) :
    At L.ports (RefreshPrepared.sourceStage T A u port hm hh sym rows zero conn L idx) z
      ((refreshWords T A u port hm hh sym rows zero conn L idx).ext z) :=
  input_wires T A u port hm hh sym rows zero conn L idx
    (selectedBits T A u port hm hh sym rows zero conn idx)
    (outputWords (Pins:=Pins) T A u port hm hh sym rows zero conn idx)
    (outputShape T A u port hm hh sym rows zero conn idx)
    (selectedOutput T A u port hm hh sym rows zero conn L idx)
    (issuedWords T A u port hm hh sym rows zero conn L idx) z

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
