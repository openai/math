import OAI.ThreeFlat.Diagonal.PhysicalRefreshTableChart
import OAI.ThreeFlat.Diagonal.PhysicalStageRefresh

namespace OAI
/-! # Installing a refresh on the numbered input while its destination words stay explicit -/

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

private theorem edgeAt (e : (A.Base × Fin m) × BitWord lanes) :
    A.width e = inputWidth ((inIso).edge e) :=
  (congrArg A.width ((StageAddress.refreshEdge u port).symm_apply_apply e)).symm

private theorem labelAt (e : (A.Base × Fin m) × BitWord lanes) (x : Fin (2^A.width e)) :
    ((inIso).label e x).val=x.val := rfl

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

set_option maxHeartbeats 160000 in
def refreshInputStage : Stage ((inIso).rewrite rule) idx L.ports.form (shapeEq.symm ▸ output.ports.form) := by
  let stage := T.wordStageOnChart src port inputWidth hm hh sym rows zero conn
    (U:=A.Site) (E:=(A.Base × Fin m) × BitWord lanes)
    (source:=A.shape.graph) (width:=A.width) (inIso) L idx bits fresh shapeEq (edgeAt A u port) (labelAt A u port)
  exact stage.reform (congrArg (fun w : WordLayout outGraph bits Pins =>
    (shapeEq.symm ▸ w.ports.form : Form ((rule).target idx) Pins)) wordsEq)

local notation "assembled" => refreshInputStage T A u port hm hh sym rows zero conn L idx bits fresh shapeEq output wordsEq

theorem refreshInputStage_count (v : (A.Base × BitWord rem) × Fin m) : (assembled).count v=1 :=
  T.wordStageOnChart_count src port inputWidth hm hh sym rows zero conn
    (source:=A.shape.graph) (width:=A.width) (inIso) L idx bits fresh shapeEq (edgeAt A u port) (labelAt A u port) v

theorem refreshInputStage_child (v : (A.Base × BitWord rem) × Fin m) (j : Fin ((assembled).count v)) :
    ((assembled).child v j).val=(inIso).site.symm v :=
  T.wordStageOnChart_child src port inputWidth hm hh sym rows zero conn
    (source:=A.shape.graph) (width:=A.width) (inIso) L idx bits fresh shapeEq (edgeAt A u port) (labelAt A u port) v j

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
