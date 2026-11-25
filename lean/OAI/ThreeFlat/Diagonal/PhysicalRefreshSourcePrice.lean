import OAI.ThreeFlat.Diagonal.PhysicalRefreshChartPrice
import OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage

namespace OAI
/-! # Resources at the numbered source of the selected refresh move -/

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

private theorem input_hidden (z : (A.Base × BitWord rem) × Fin m) :
    (assembled).hidden z = L.ports.halfBits ((inIso).site.symm z) :=
  T.wordStageOnChart_hidden src port inputWidth hm hh sym rows zero conn
    (source:=A.shape.graph) (width:=A.width) (inIso) L idx bits fresh shapeEq (edgeAt A u port) (labelAt A u port) z

private theorem input_width (z : (A.Base × BitWord rem) × Fin m) :
    (assembled).rootWidth z = L.ports.halfBits ((inIso).site.symm z) + fresh.ports.halfBits z :=
  T.wordStageOnChart_width src port inputWidth hm hh sym rows zero conn
    (source:=A.shape.graph) (width:=A.width) (inIso) L idx bits fresh shapeEq (edgeAt A u port) (labelAt A u port) z

private theorem input_price (z : (A.Base × BitWord rem) × Fin m) (K height : ℕ)
    (fee : refreshTariff c (fun a => T.base (T.winner src port inputWidth a))
      (T.entry src port inputWidth) z.1 z.2 ≤ K)
    (room : HistogramTileNetwork.siteHeight (T.repeats src port inputWidth z.1)
      (T.entry src port inputWidth z.1).bitCap ≤ height) :
    (assembled).freshResources z ≤ (2+K)*(height+1)^3*(1+(L.ports.halfBits ((inIso).site.symm z)+
      fresh.ports.halfBits z)+T.repeats src port inputWidth z.1) :=
  T.wordStageOnChart_price src port inputWidth hm hh sym rows zero conn
    (source:=A.shape.graph) (width:=A.width) (inIso) L idx bits fresh shapeEq (edgeAt A u port) (labelAt A u port)
    z K height fee room

end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage
open LinearAlgebra.SpectralBooks Expander Computability.VPVNP.Compression CompressorPacking HistoryContraction
open scoped Classical BigOperators
noncomputable section

variable {F Pins : Type} [Field F] {m lanes hbits rem h pad : ℕ} {c : Fin m→Fin m→ℕ} {C γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) C) (A : State m lanes)
  (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
  (hm : 2 ≤ m) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (zero : ∀ i,c i i=0) (conn : Bound (transition c h) ℝ γ)

set_option quotPrecheck false

local notation "physMove" => refreshMove T A u port hm hh sym rows zero conn
local notation "inIso" => StageAddress.refreshInputIso A.graph A.chart u port A.width

attribute [local irreducible] CompressorRefresh.graph RefreshTies.freshWidth
  RefreshMotif.Table.wordStageOnChart RefreshTies.refreshAssemblyAtWidth

section
variable (L : A.Words Pins) (idx : Fin (refreshMove T A u port hm hh sym rows zero conn).rules.count)

local notation "inputGraph" => changeLanes A.graph u
local notation "inputWidth" => refreshInput A u port
local notation "outGraph" => RefreshTies.actualPortGraph (RefreshTies.outputGraph inputGraph c sym rows zero hm pad)
local notation "rule" => T.step inputGraph port inputWidth hm hh sym rows zero conn

open private selectedBits outputWords outputShape selectedOutput issuedWords
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage

local notation "sourceStage" => RefreshPrepared.sourceStage T A u port hm hh sym rows zero conn L idx
local notation "selected" => outputWords (Pins:=Pins) T A u port hm hh sym rows zero conn idx

theorem RefreshPrepared.source_hidden (z : (A.Base × BitWord rem) × Fin m) :
    (sourceStage).hidden z=L.ports.halfBits ((inIso).site.symm z) :=
  input_hidden T A u port hm hh sym rows zero conn L idx
    (selectedBits T A u port hm hh sym rows zero conn idx) selected
    (outputShape T A u port hm hh sym rows zero conn idx)
    (selectedOutput T A u port hm hh sym rows zero conn L idx)
    (issuedWords T A u port hm hh sym rows zero conn L idx) z

theorem RefreshPrepared.source_width (z : (A.Base × BitWord rem) × Fin m) :
    (sourceStage).rootWidth z=L.ports.halfBits ((inIso).site.symm z)+(selected).ports.halfBits z :=
  input_width T A u port hm hh sym rows zero conn L idx
    (selectedBits T A u port hm hh sym rows zero conn idx) selected
    (outputShape T A u port hm hh sym rows zero conn idx)
    (selectedOutput T A u port hm hh sym rows zero conn L idx)
    (issuedWords T A u port hm hh sym rows zero conn L idx) z

theorem RefreshPrepared.source_price (z : (A.Base × BitWord rem) × Fin m) (K height : ℕ)
    (fee : RefreshTies.refreshTariff c (fun a=>T.base (T.winner inputGraph port inputWidth a))
      (T.entry inputGraph port inputWidth) z.1 z.2 ≤ K)
    (room : HistogramTileNetwork.siteHeight (T.repeats inputGraph port inputWidth z.1)
      (T.entry inputGraph port inputWidth z.1).bitCap ≤ height) :
    (sourceStage).freshResources z ≤ (2+K)*(height+1)^3*(1+(L.ports.halfBits ((inIso).site.symm z)+
      (selected).ports.halfBits z)+T.repeats inputGraph port inputWidth z.1) :=
  input_price T A u port hm hh sym rows zero conn L idx
    (selectedBits T A u port hm hh sym rows zero conn idx) selected
    (outputShape T A u port hm hh sym rows zero conn idx)
    (selectedOutput T A u port hm hh sym rows zero conn L idx)
    (issuedWords T A u port hm hh sym rows zero conn L idx) z K height fee room


end
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
