import OAI.Hierarchy.ProbeShapeMenus
import OAI.Hierarchy.ProtocolRAMCalendarStripChart
import OAI.Hierarchy.ProbeMenuSizes

namespace OAI
/-! # One finite alphabet, coefficient bound and copy count for the two installed strip catalogues -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseStage
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical BigOperators

namespace Calendar.StripChart

open StripDirectory
variable {z d k q depth : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))

variable (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (s : Boards z d k q depth) (cost : TreeCosts)

def catalogue :=
  letI : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,s.positive⟩⟩
  letI : Nonempty (PurchasedRole depth k) := ⟨.catalyst (ChainStrip.inlet depth 0) ⟨0,s.positive⟩⟩
  let a := payloadMenu F N k s.positive s.radius s.radius_nonneg s.tolerance s.tolerance_pos
    cost.payload cost.payload_nonneg s.minimum
  let b := purchasedMenu F depth k s.positive s.radius s.radius_nonneg s.tolerance s.tolerance_pos
    cost.purchase cost.purchase_nonneg s.minimum
  (PacketWidths.ofMenu a).either (PacketWidths.ofMenu b)

/-- Retarget the initial repair-board alphabet. The actual strip compiler
subsequently fills all selector and wire expressions from its own finite menu. -/
def repairAlphabet {n : ℕ} (Q : ℕ) (b : Repair q n) : Repair Q n :=
  { b with
    batch := {b.batch with field:=PortPadding.extend b.batch.field (.lit 0)}
    reportWidth := PortPadding.extend b.reportWidth (.lit 0)
    wire := fun i=>PortPadding.extend (b.wire i) (.lit 0) }

def localDimensions {digits ports : ℕ} (Q bound multiplicity : ℕ)
    (b : StripDirectory.Boards z d k q digits ports) : StripDirectory.Boards z d k Q digits ports :=
  {b with repair:=repairAlphabet Q b.repair,maxWidth:=bound,copies:=multiplicity}

/-- No polynomial bound on packet size is used. Each of the two fixed compact
catalogues is finite before the growing instance and its private input are chosen. -/
def withMenuSizes (scale width : ℕ) : Boards z d k (catalogue F s cost).alphabet depth :=
  let menu := catalogue F s cost
  let localize := fun {digits ports : ℕ} (b : StripDirectory.Boards z d k q digits ports) =>
    localDimensions menu.alphabet menu.maximum (menu.copiesAt scale width) b
  { s with
    tree := cost.atAttempt
    tree_nonneg := cost.nonneg
    outer := fun p a => localize (s.outer p a)
    inner := fun p a j t => localize (s.inner p a j t) }

theorem actual_width (scale width addr : ℕ) (a : Attempt) :
    let menu := catalogue F s cost
    let f := build F (withMenuSizes F s cost scale width) a addr
    f.batch.batch.maxWidth=menu.maximum ∧ f.histMass=menu.copiesAt scale width := by cases a <;> exact ⟨rfl,rfl⟩

end Calendar.StripChart
end Hierarchy.ProtocolRAM
end

end OAI
