import OAI.Hierarchy.ProbeFixedPhase
import OAI.Hierarchy.ProtocolRAMCalendarChargePages
import OAI.Hierarchy.ProtocolRAMCatalystSlabLayout
import OAI.Hierarchy.ProbeStripChartTests
import OAI.Hierarchy.ProtocolRAMCalendarStripHistFields
import OAI.Hierarchy.ProtocolRAMCalendarStripForestHeader

namespace OAI
/-! # Address-resolved installation of the two strip procedures on the fixed mesh -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseCT StripDirectory StripChart CatalogueRows
open scoped Fin.CommRing Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)
  {z raw : ℕ} (origin : Boards z (2^v.W) k raw v.depth)

/-- The sole per-height inputs for locating public banks; no threshold,
packet choice, selected flag or label is stored in this description. -/
structure Placement where
  joint : JointHeader.Board
  catalogue : CatalogueRows.Board
  routes : PortBanks ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)

def sized (width : ℕ) := withMenuSizes F (v.configured origin) v.cost v.copyScale width

/-- Compute all public addresses before emitting an expression that references a purchased shelf. -/
def header (whereAt : v.Placement) (width : ℕ) :=
  economicHeader F (v.sized origin width) v.cost v.mesh whereAt.joint whereAt.catalogue whereAt.routes
    v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision

def slab (whereAt : v.Placement) (width : ℕ) :=
  let prior:=chargedSlab F (v.sized origin width) v.cost (v.header origin whereAt width) (ProtocolRAMPurchaseSampler.bits v.keepLimit)
  prior.withTerminal v.mesh z (2^v.W) k (v.sized origin width).sampler.degree v.depth whereAt.catalogue.rows

def located (whereAt : v.Placement) (width : ℕ) :=
  (v.slab origin whereAt width).install (v.sized origin width) v.mesh

/-- The actual shelf at each outer trial is resolved before the inner role's
port expression is emitted, including the archived candidate and its mate. -/
def mounted (whereAt : v.Placement) (width : ℕ) :=
  let H := v.header origin whereAt width
  let scheduled := v.located origin whereAt width
  let labelled := withPorts scheduled v.mesh whereAt.catalogue whereAt.routes
  let historical := withPurchaseFields labelled v.mesh whereAt.catalogue whereAt.routes
  let priced := withPublicROM historical whereAt.joint v.mesh v.finish (v.basePhase width)
  let discrepancies := withDiscrepancy priced (DeadlineROM.index v.mesh) H.payload H.bought
    v.precision v.precision v.toleranceAt
  let menus := withMenuROM F discrepancies v.cost H.bought.stop v.digitRadix v.digitRadix
    (DeadlineROM.prices v.mesh v.finish (v.basePhase width)) (DeadlineROM.index v.mesh)
  withCharges F menus v.cost H.stop

def physicalTrees (whereAt : v.Placement) (width : ℕ) (u : Attempt) :=
  let H := v.header origin whereAt width
  let located := v.located origin whereAt width
  let old := originalTree located v.mesh whereAt.catalogue whereAt.routes F H.payloadTree.base u
  let directory := StripChart.header F (v.mounted origin whereAt width) u
  forestAtHeader located v.mesh whereAt.catalogue whereAt.routes directory old u

def arena (whereAt : v.Placement) (width : ℕ) :=
  (v.slab origin whereAt width).arena (v.sized origin width)

private theorem outerDimensions {q₀ : ℕ} (s : StripChart.Boards z (2^v.W) k q₀ v.depth)
    (phase trial incoming : ℕ) :
    let stage := build F s (.outer phase trial) incoming
    stage.batch.batch.maxWidth = (s.outer phase trial).maxWidth ∧
      stage.histMass = (s.outer phase trial).copies := ⟨rfl, rfl⟩

private theorem innerDimensions {q₀ : ℕ} (s : StripChart.Boards z (2^v.W) k q₀ v.depth)
    (phase trial window step incoming : ℕ) :
    let stage := build F s (.inner phase trial window step) incoming
    stage.batch.batch.maxWidth = (s.inner phase trial window step).maxWidth ∧
      stage.histMass = (s.inner phase trial window step).copies := ⟨rfl, rfl⟩

theorem literal_dimensions (whereAt : v.Placement) (width incoming : ℕ) (u : Attempt) :
    let stage:=build F (v.mounted origin whereAt width) u incoming
    stage.batch.batch.maxWidth=v.menu.maximum ∧ stage.histMass=v.menu.copiesAt v.copyScale width := by
  let s := v.mounted origin whereAt width
  have words := v.catalogue_words origin width
  cases u with
  | outer phase trial =>
    have fields := outerDimensions v s phase trial incoming
    exact ⟨fields.1.trans words.2.1, fields.2.trans words.2.2⟩
  | inner phase trial window step =>
    have fields := innerDimensions v s phase trial window step incoming
    exact ⟨fields.1.trans words.2.1, fields.2.trans words.2.2⟩

theorem purchase_port (whereAt : v.Placement) (width p a j b : ℕ) :
    let s:=v.mounted origin whereAt width
    s.purchaseEdge p a j b=purchaseEdge
      (boughtPortsAt (v.located origin whereAt width) v.mesh whereAt.catalogue whereAt.routes p a) whereAt.catalogue :=
  rfl

theorem outer_shelf (whereAt : v.Placement) (width p a : ℕ) :
    let s:=v.mounted origin whereAt width
    let z₀:=v.slab origin whereAt width
    (s.outer p a).market.shelf.firstBase=z₀.first (v.sized origin width)
      ((v.arena origin whereAt width).base v.mesh (.attempt (.outer p a))) := rfl

theorem payment_banks (whereAt : v.Placement) (width p a j b : ℕ) :
    let s:=v.mounted origin whereAt width
    let H:=v.header origin whereAt width
    let price:=charges F (v.sized origin width) v.cost H.stop
    (s.outer p a).cash=price.payload.bank 0 ∧ (s.inner p a j b).cash=price.purchase.bank 0 :=
  ⟨rfl,rfl⟩

theorem discrepancy_banks (whereAt : v.Placement) (width p a j b : ℕ) :
    let s:=v.mounted origin whereAt width
    let H:=v.header origin whereAt width
    (s.outer p a).test.table=H.payload.bank (DeadlineROM.index v.mesh (.outer p a)) ∧
    (s.inner p a j b).test.table=H.bought.bank (DeadlineROM.index v.mesh (.inner p a j b)) :=
  ⟨rfl,rfl⟩

theorem selection_banks (whereAt : v.Placement) (width p a j b : ℕ) :
    let s:=v.mounted origin whereAt width
    let H:=v.header origin whereAt width
    (s.outer p a).menu=H.menus.left.bank (DeadlineROM.index v.mesh (.outer p a)) ∧
    (s.inner p a j b).menu=H.menus.right.bank (DeadlineROM.index v.mesh (.inner p a j b)) ∧
    (s.outer p a).terms=H.menus.leftAlphabet.bank 0 ∧ (s.inner p a j b).terms=H.menus.rightAlphabet.bank 0 :=
  ⟨rfl,rfl,rfl,rfl⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
