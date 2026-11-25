import OAI.Hierarchy.TaggedWidePlacement
import OAI.Hierarchy.ProtocolRAMCalendarEconomicSize

namespace OAI
/-! # Uniform size of the menu, economic archive and reserve prefix -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripDirectory StripChart CoreBoard
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

/-- Number of entries in each of the two actual packet dictionaries at a given stage count. -/
def wideMenuCard (N : ℕ) : ℕ × ℕ := by
  letI : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
  letI : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  let a:=payloadMenu F N k v.positive v.radius (Nat.cast_nonneg _) v.toleranceAt v.geometry.cutoff.1
    v.cost.payload v.cost.payload_nonneg 0
  let b:=purchasedMenu F v.depth k v.positive v.radius (Nat.cast_nonneg _) v.toleranceAt v.geometry.cutoff.1
    v.cost.purchase v.cost.purchase_nonneg 0
  exact (Fintype.card a.index,Fintype.card b.index)

def wideEconomicFactor (N : ℕ) :=
  let phases:=DeadlineROM.count v.mesh
  let D:=max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
  let h:=JointHeader.coefficient N k phases v.mesh.reserveSteps+
    (12*(((N*(2*k))*v.sampler.degree^v.depth)*D)+8)+phases*(2*(GlobalTests.kinds N k+1))
  let m:=v.wideMenuCard N
  h+2*vectorCharge N k v.depth phases v.digitRadix v.digitRadix+
    (2*((m.1+1)+1)+2*((m.2+1)+1))+
    treePagesFactor v.mesh (2^v.W) k v.sampler.degree v.depth

theorem wideEconomicHeader (h width : ℕ) (stride : v.keepLimit*width+1≤2^h) :
    let P:=v.widePlacement h width
    (v.publicHeader P h width).stop≤P.joint.initial+v.wideEconomicFactor (publicStages v.W)*2^h := by
  let P:=v.widePlacement h width
  let s:=v.sized (v.seed P h width) width
  have bound:=StripChart.economic_header_linear F s v.cost v.mesh P.joint P.catalogue P.routes
    v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision stride
  change (v.publicHeader P h width).stop≤P.joint.initial+v.wideEconomicFactor (Stages h (2^v.W))*2^h at bound
  simpa only [show Stages h (2^v.W)=publicStages v.W from fixed_stage_count h v.W] using bound

theorem wideEconomicHeight :
    ∃c:ℕ,∀ h width,v.keepLimit*width+1≤2^h →
      (v.publicHeader (v.widePlacement h width) h width).stop≤c*2^h := by
  obtain ⟨c,first⟩:=v.wideGeometryHeight
  refine ⟨c+v.wideEconomicFactor (publicStages v.W),fun h width fit=>?_⟩
  rw [Nat.add_mul]
  exact (v.wideEconomicHeader h width fit).trans (Nat.add_le_add_right (first h width) _)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
