import OAI.ThreeFlat.Diagonal.PhysicalRefreshWordInputs
import OAI.ThreeFlat.Diagonal.PhysicalRefreshInputStage

namespace OAI
/-! # Preparing the selected native refresh stage and its physical output form -/

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

private def selectedBits : RefreshTies.LiveSlot A.Base (BitWord rem) m (1+h+pad) → ℕ :=
  ((physMove).next idx).width

private def outputWords : WordLayout outGraph (selectedBits T A u port hm hh sym rows zero conn idx) Pins :=
  ((physMove).next idx).halfWords Pins

private theorem outputShape : (rule).target idx = WordLayout.shape outGraph (selectedBits T A u port hm hh sym rows zero conn idx) :=
  (physMove).target_eq idx

private def selectedOutput : WordLayout outGraph (selectedBits T A u port hm hh sym rows zero conn idx) Pins :=
  refreshWords T A u port hm hh sym rows zero conn L idx

private theorem issuedWords :
    ((inIso).pushWord (H:=RefreshTies.oldPortGraph (RefreshTies.arrival inputGraph port)) (b:=inputWidth) L).inherited
      (outputWords (Pins:=Pins) T A u port hm hh sym rows zero conn idx) id (fun _=>1) RefreshTies.singleChild =
      selectedOutput T A u port hm hh sym rows zero conn L idx := rfl

/-- Read a word layout using the supplied site and edge enumerations. -/
private abbrev numberedForm {V E P : Type} (sites : Fintype V) (edges : Fintype E)
    {graph : PortGraph V E} {bits : E → ℕ} (word : WordLayout graph bits P) :=
  letI : Fintype V := sites
  letI : Fintype E := edges
  word.ports.form

private theorem numberedForm_eq {V E P : Type} {S : Shape}
    (sites₁ sites₂ : Fintype V) (edges₁ edges₂ : Fintype E)
    {rawGraph nativeGraph : PortGraph V E} {rawBits nativeBits : E → ℕ}
    (graphs : rawGraph = nativeGraph) (widths : rawBits = nativeBits)
    (raw : WordLayout rawGraph rawBits P) (native : WordLayout nativeGraph nativeBits P)
    (same : HEq raw native)
    (first : S = @WordLayout.shape V E sites₁ edges₁ rawGraph rawBits)
    (second : S = @WordLayout.shape V E sites₂ edges₂ nativeGraph nativeBits) :
    (first.symm ▸ numberedForm sites₁ edges₁ raw : Form S P) =
      second.symm ▸ numberedForm sites₂ edges₂ native := by
  cases graphs
  cases widths
  cases eq_of_heq same
  cases Subsingleton.elim sites₁ sites₂
  cases Subsingleton.elim edges₁ edges₂
  rfl

private theorem sameGraph :
    outGraph = ((physMove).next idx).shape.graph := rfl

private theorem sameBits :
    selectedBits T A u port hm hh sym rows zero conn idx = ((physMove).next idx).width := rfl

/-- The chart view and the physical output contain the same issued words. -/
private theorem sameIssuedOutput :
    HEq (selectedOutput T A u port hm hh sym rows zero conn L idx)
      (refreshWords T A u port hm hh sym rows zero conn L idx) := HEq.rfl

attribute [local irreducible] refreshInputStage WordLayout.ports PortLayout.form
  selectedBits selectedOutput

set_option maxHeartbeats 110000 in
private def atIndex :=
  refreshInputStage (F:=F) (Pins:=Pins) (m:=m) (lanes:=lanes) (hbits:=hbits) (rem:=rem)
    (h:=h) (pad:=pad) (c:=c) (C:=C) (γ:=γ) T A u port hm hh sym rows zero conn L idx

set_option maxHeartbeats 110000 in
private def atWidth :=
  atIndex T A u port hm hh sym rows zero conn L idx
    (selectedBits T A u port hm hh sym rows zero conn idx)
    (outputWords (Pins:=Pins) T A u port hm hh sym rows zero conn idx)

set_option maxHeartbeats 110000 in
private def atShape :=
  atWidth T A u port hm hh sym rows zero conn L idx
    (outputShape T A u port hm hh sym rows zero conn idx)
    (selectedOutput T A u port hm hh sym rows zero conn L idx)

set_option maxHeartbeats 110000 in
/-- The stage installed by the source chart at the selected table row. -/
def RefreshPrepared.sourceStage :=
  atShape T A u port hm hh sym rows zero conn L idx
    (issuedWords T A u port hm hh sym rows zero conn L idx)

private def installNumbered {K P : Type} [Field K] {d l D n : ℕ} {source : State d l}
    (r : Move K source D n) (i : Fin r.rules.count) (input : source.Words P) (output : (r.next i).Words P)
    (sites : Fintype (r.next i).Site) (edges : Fintype (((r.next i).Base × Fin D) × BitWord n))
    (graph : PortGraph (r.next i).Site (((r.next i).Base × Fin D) × BitWord n))
    (bits : ((r.next i).Base × Fin D) × BitWord n → ℕ)
    (word : WordLayout graph bits P)
    (shape : r.rules.target i = @WordLayout.shape _ _ sites edges graph bits)
    (graphEq : graph = (r.next i).shape.graph) (bitsEq : bits = (r.next i).width)
    (wordEq : HEq word output)
    (stage : Stage r.rules i input.ports.form (shape.symm ▸ numberedForm sites edges word)) :
    StageFor r i input output :=
  stage.reform (numberedForm_eq sites (r.next i).finiteSite edges (r.next i).shape.edgeFintype
    graphEq bitsEq word output wordEq shape (r.target_eq i))

set_option maxHeartbeats 110000 in
private def installAt :=
  installNumbered (physMove) idx L (refreshWords T A u port hm hh sym rows zero conn L idx)

set_option maxHeartbeats 110000 in
private def sitesAt :=
  installAt T A u port hm hh sym rows zero conn L idx
    (inferInstance : Fintype ((A.Base × BitWord rem) × Fin m))

set_option maxHeartbeats 110000 in
private def edgesAt :=
  sitesAt T A u port hm hh sym rows zero conn L idx
    (inferInstance : Fintype (RefreshTies.LiveSlot A.Base (BitWord rem) m (1+h+pad)))

set_option maxHeartbeats 110000 in
private def graphAt :=
  edgesAt T A u port hm hh sym rows zero conn L idx
    outGraph

set_option maxHeartbeats 110000 in
private def bitsAt :=
  graphAt T A u port hm hh sym rows zero conn L idx
    (selectedBits T A u port hm hh sym rows zero conn idx)

set_option maxHeartbeats 110000 in
private def wordsAt :=
  bitsAt T A u port hm hh sym rows zero conn L idx
    (selectedOutput T A u port hm hh sym rows zero conn L idx)

set_option maxHeartbeats 110000 in
private def atTable :=
  wordsAt T A u port hm hh sym rows zero conn L idx
    (outputShape T A u port hm hh sym rows zero conn idx)

set_option maxHeartbeats 110000 in
/-- Install a stage on the physical output graph, using its actual words and port order. -/
def RefreshPrepared.install :=
  atTable T A u port hm hh sym rows zero conn L idx
    (sameGraph T A u port hm hh sym rows zero conn idx)
    (sameBits T A u port hm hh sym rows zero conn idx)
    (sameIssuedOutput T A u port hm hh sym rows zero conn L idx)

end
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
