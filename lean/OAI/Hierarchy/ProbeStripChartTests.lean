import OAI.Hierarchy.ProtocolRAMCalendarStripPublicROM
import OAI.Hierarchy.ProbeDiscrepancyROM

namespace OAI
/-! # The real purchased strip field inside the common padded controller -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage StripDirectory
open scoped Classical
variable {z d k q depth phases : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

theorem bought_test (c : Mesh) (arena : Arena) (initial : ℕ) (s : Boards z d k q depth) (p a j b : ℕ) :
    let fm:=formats F c arena initial s
    let inner:=s.inner p a j b
    let u:=Attempt.inner p a j b
    let st:={inner.old with base:=(fm u).market.shelf.stockBase}
    (fm u).market.failures=(checkedPurchase (z:=z) (d:=d) (fm (.outer p a)).market.shelf s.sampler
      (s.stratumHeader p a) inner.test inner.price (GlobalTests.offsets inner.globalTests) st).failure := rfl

/-- No native payload test row outside the original payload prefix can become
active: its runtime live instruction compares against the true number of records. -/
theorem payload_effective (c : Mesh) (arena : Arena) (initial : ℕ) (s : Boards z d k q depth) (p a : ℕ) :
    let fm:=formats F c arena initial s
    let outer:=s.outer p a
    let u:=Attempt.outer p a
    let st:={outer.old with base:=(fm u).market.shelf.stockBase}
    let real:=checkedPayload z N k outer.test outer.price (GlobalTests.offsets outer.globalTests) st
    (fm u).market.failures.effective=real.failure.effective ∧
      (fm u).market.failures.cut=real.failure.cut ∧ (fm u).market.failures.globalBound=real.failure.globalBound :=
  ⟨rfl,rfl,rfl⟩

/-- Public chart compiler binds the appropriate table bank as an immediate.
No evaluated answer, matching, failure flag or packet is put in the initial
memory. The two kinds may have different local arities, radices and precision. -/
def withDiscrepancy (s : Boards z d k q depth) (phaseAt : Attempt→Fin phases)
    (outer : DiscrepancyROM.Table phases (Fintype.card (PayloadStrip.Quotes N k)))
    (inner : DiscrepancyROM.Table phases (Fintype.card (ChainStrip.Axes depth k)))
    (outerPrecision innerPrecision : ℕ) (tol : ℝ) : Boards z d k q depth :=
  {s with
    outer:=fun p a=>let v:=s.outer p a
      {v with test:={v.test with table:=outer.bank (phaseAt (.outer p a)),radix:=outer.radix,precision:=outerPrecision,tolerance:=tol}}
    inner:=fun p a j b=>let v:=s.inner p a j b
      {v with test:={v.test with table:=inner.bank (phaseAt (.inner p a j b)),radix:=inner.radix,precision:=innerPrecision,tolerance:=tol}}}

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
