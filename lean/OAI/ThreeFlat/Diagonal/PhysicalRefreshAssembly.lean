import OAI.ThreeFlat.Diagonal.PhysicalRefreshWordPrice
import OAI.ThreeFlat.Diagonal.PhysicalRefreshPortMeasurements
import OAI.ThreeFlat.Diagonal.PhysicalProgramRecords
import OAI.ThreeFlat.Diagonal.PhysicalRefreshWords
import OAI.ThreeFlat.Diagonal.PhysicalStageBinary

namespace OAI
/-! # Assembling the physical refresh with the actual successor half-port order -/

namespace ThreeFlat.Diagonal.PhysicalStage
open LinearAlgebra.SpectralBooks Expander Computability.VPVNP.Compression CompressorPacking HistoryContraction
open scoped Classical BigOperators
noncomputable section

variable {F Pins : Type} [Field F]

/-- A changed successor degree leaves the selected rewrite target and its sites unchanged. -/
def Program.degreeTarget {d l D D' t : ℕ} {S₀ : State d l} (e : D=D') (M₀ : Move F S₀ D t)
    (j : Fin M₀.rules.count) :
    ((Program.recastMove e M₀).rules.target (Program.degreeTerm e M₀ j)).Site ≃ (M₀.rules.target j).Site := by
  cases e
  exact Equiv.refl _

private def installedRoot {d l D t : ℕ} {X : State d l} (M : Move F X D t)
    (J : M.Assembler Pins) (L : X.Words Pins) (i : Fin M.rules.count)
    (v : (M.rules.target i).Site) : Tree F ((J L i).stage.rootWidth v) :=
  (J L i).stage.root v

private theorem installedRoot_degree {d l D D' t : ℕ} {X : State d l} (e : D=D')
    (M : Move F X D t) (J : M.Assembler Pins) (L : X.Words Pins) (i : Fin M.rules.count)
    (v : ((Program.recastMove e M).rules.target (Program.degreeTerm e M i)).Site) :
    let step := Move.outputAssembler e M J L (Program.degreeTerm e M i)
    (⟨step.stage.rootWidth v,step.stage.root v⟩ : Σ p,Tree F p) =
      ⟨_,installedRoot M J L i (Program.degreeTarget e M i v)⟩ := by
  cases e
  rfl

section ActualRoot
variable {s₀ n h₀ p₀ : ℕ} {matrix : Fin (2^s₀)→Fin (2^s₀)→ℕ} {K gap : ℝ}
    (tile : RefreshMotif.Table F matrix (1+h₀+p₀) K) (S₀ : State (2^s₀) (s₀+n))
    (ports : 2≤2^s₀) (positive : 0<h₀) (symmetric : ∀ i j,matrix i j=matrix j i)
    (row : ∀ i,∑ j,matrix i j=h₀) (noLoop : ∀ i,matrix i i=0)
    (connected : Bound (transition matrix h₀) ℝ gap)

set_option quotPrecheck false

local notation "split₀" => splitWord s₀ n
local notation "tag₀" => (Native.tagOrdinal s₀).symm
local notation "G₀" => changeLanes S₀.graph split₀
local notation "w₀" => refreshInput S₀ split₀ tag₀
local notation "I₀" => StageAddress.refreshInputIso S₀.graph S₀.chart split₀ tag₀ S₀.width
local notation "M₀" => refreshBinary tile S₀ ports positive symmetric row noLoop connected
local notation "R₀" => tile.step G₀ tag₀ w₀ ports positive symmetric row noLoop connected
local notation "J₀" => refreshBinary_assembler tile S₀ ports positive symmetric row noLoop connected
variable (L₀ : S₀.Words Pins)
  (j₀ : Fin (refreshBinary tile S₀ ports positive symmetric row noLoop connected).rules.count)
local notation "pushed" => (I₀).pushWord L₀
local notation "fresh₀" => ((M₀).next j₀).halfWords Pins
/-- The direct-party kernel installed by the binary refresh, at the actual chart
site and selected branch of the word assembler. -/
def refreshBinary_siteTree :=
  installedRoot M₀ J₀ L₀ j₀

variable {D₀ : ℕ} (deg : 1+h₀+p₀=D₀)
local notation "b₀" => Program.degreeTerm deg M₀ j₀
local notation "ws₀" => Move.outputAssembler deg M₀ J₀ L₀ b₀
local notation "site₀" => Program.degreeTarget deg M₀ j₀

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- Equality of both the pin arity and the literal tree after the program's successor-degree cast. -/
theorem refreshBinary_assembler_root (z : ((Program.recastMove deg M₀).rules.target b₀).Site) :
    (⟨(ws₀).stage.rootWidth z,(ws₀).stage.root z⟩ : Σ p,Tree F p)=
      ⟨_,refreshBinary_siteTree tile S₀ ports positive symmetric row noLoop connected L₀ j₀ (site₀ z)⟩ :=
  installedRoot_degree deg M₀ J₀ L₀ j₀ z

open RefreshReadback

section Measurements
variable {d l D t : ℕ} {A : State d l} (R : Move F A D t) (L : A.Words Pins)
    (b : Fin R.rules.count) (step : R.WordStep Pins L b) (site : (R.rules.target b).Site)

/-- Read the delivered width from any ordered word layout on the same successor. -/
private theorem single_numbered (owner : A.Site) (fresh : (R.next b).Words Pins)
    (out : (R.next b).Site) (reached : cast (congrArg Shape.Site (R.target_eq b)) site = out)
    (count : step.stage.count site = 1) (child : ∀ k, (step.stage.child site k).val = owner)
    (hidden : step.stage.hidden site = L.ports.halfBits owner)
    (width : step.stage.rootWidth site = L.ports.halfBits owner + fresh.ports.halfBits out) :
    singleMeasurements R L b step site owner := by
  have landed := (transportedHalf (R.target_eq b) step.words.ports site).trans
    (congrArg step.words.ports.halfBits reached)
  have same := (wordHalf_order (R.next b) fresh step.words out).trans landed.symm
  exact ⟨count,child,hidden,width.trans (congrArg (fun n => L.ports.halfBits owner + n) same),
    single_target R L b step site owner count child⟩

private theorem measured_degree {D' : ℕ} (eqn : D=D') (J : R.Assembler Pins)
    (whereAt : (R.rules.target b).Site → A.Site)
    (h : ∀ z,singleMeasurements R L b (J L b) z (whereAt z))
    (z : ((Program.recastMove eqn R).rules.target (Program.degreeTerm eqn R b)).Site) :
    singleMeasurements (Program.recastMove eqn R) L (Program.degreeTerm eqn R b)
      (Move.outputAssembler eqn R J L (Program.degreeTerm eqn R b)) z
      (whereAt (Program.degreeTarget eqn R b z)) := by
  cases eqn
  exact h z

end Measurements

private theorem cast_site_self {U : Type} (same : U=U) (z : U) : cast same z=z := rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private def oldSite (z : ((M₀).rules.target j₀).Site) : S₀.Site := (I₀).site.symm z

set_option maxRecDepth 8192 in
set_option maxHeartbeats 220000 in
private theorem uncastPorts (z : (S₀.Base × BitWord n) × Fin (2^s₀)) :
    singleMeasurements M₀ L₀ j₀ (J₀ L₀ j₀) z (oldSite tile S₀ ports positive symmetric row noLoop connected j₀ z) := by
  have physical := @cast_site_self ((S₀.Base × BitWord n) × Fin (2^s₀))
    (congrArg Shape.Site ((M₀).target_eq j₀)) z
  exact single_numbered M₀ L₀ j₀ (J₀ L₀ j₀) z
    (oldSite tile S₀ ports positive symmetric row noLoop connected j₀ z) fresh₀ z physical
    (refreshMove_stageCount tile S₀ split₀ tag₀ ports positive symmetric row noLoop connected L₀ j₀ z)
    (refreshMove_stageChild tile S₀ split₀ tag₀ ports positive symmetric row noLoop connected L₀ j₀ z)
    (refreshWordStage_hidden tile S₀ split₀ tag₀ ports positive symmetric row noLoop connected L₀ j₀ z)
    (refreshWordStage_width tile S₀ split₀ tag₀ ports positive symmetric row noLoop connected L₀ j₀ z)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- Readback of the chart stage's single inherited child, hidden bank and kernel arity. -/
theorem refreshBinary_assembler_ports (z : ((Program.recastMove deg M₀).rules.target b₀).Site) :
    singleMeasurements (Program.recastMove deg M₀) L₀ b₀ ws₀ z
      (oldSite tile S₀ ports positive symmetric row noLoop connected j₀ (site₀ z)) :=
  measured_degree M₀ L₀ j₀ deg J₀ _ (uncastPorts tile S₀ ports positive symmetric row noLoop connected L₀ j₀) z

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- The selected root reads every old and new half bit in its chronological port layouts. -/
theorem refreshBinary_assembler_arity (z : ((Program.recastMove deg M₀).rules.target b₀).Site) :
    rootMeasurements (Program.recastMove deg M₀) L₀ b₀ ws₀ z :=
  single_root (Program.recastMove deg M₀) L₀ b₀ ws₀ z
    (refreshBinary_assembler_ports tile S₀ ports positive symmetric row noLoop connected L₀ j₀ deg z)

end ActualRoot

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
