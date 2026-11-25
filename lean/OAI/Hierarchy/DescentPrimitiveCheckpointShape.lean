import OAI.Hierarchy.DescentDatedNodeMetadataRate

namespace OAI
/-! # Addresses for the immutable global primitive-role archive after a reset -/
namespace Hierarchy.DescentResetPrimitiveCheckpoint
open DescentDatedAddressBook DescentSIMDLookup Filter
noncomputable section
structure Shape where
  chart : DescentDatedNodeMetadata.Chart
  rawBits : ℕ
namespace Shape
variable (v : Shape)
def gateEnd (base : ℕ) :=base+2*2^(v.rawBits*v.chart.lanes)+2*2^v.chart.lanes
def scalarEnd (base : ℕ) :=v.gateEnd base+(v.chart.blocks*v.chart.nodes)*v.chart.rows
def out (base : ℕ) :=v.scalarEnd base+max v.chart.dictionary v.chart.rounded
def endAddress (base : ℕ) :=v.out base+v.chart.blocks*v.chart.rows+v.chart.rounded
def bank (base : ℕ) (x : Fin v.chart.blocks) : ProtocolRAM.Bank :=
  ⟨v.out base+x.val*v.chart.rows,Nat.clog 2 (v.chart.rows+1)⟩
theorem translate (base : ℕ) : v.endAddress base=base+v.endAddress 0:=by
  simp only [endAddress,out,scalarEnd,gateEnd,Nat.zero_add,Nat.add_assoc]

variable {ι : ℕ→Type*} (p : ∀h,ι h→Shape)
structure ScalarRoom : Prop where
  chart : DescentDatedNodeMetadata.Chart.ScalarRoom (fun h i=>(p h i).chart)
  raw : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let v:=p h i;max (v.rawBits*v.chart.lanes) v.chart.lanes≤K*h

theorem rate (room : ScalarRoom p) : Bounded (fun h i=>(p h i).endAddress 0):=by
  obtain ⟨K,hk⟩:=room.raw
  have a:=Bounded.pow_of_linear (K:=K) (hk.mono fun h H i=>(Nat.le_max_left ..).trans (H i))
  have b:=Bounded.pow_of_linear (K:=K) (hk.mono fun h H i=>(Nat.le_max_right ..).trans (H i))
  have old:=DescentDatedNodeMetadata.Chart.extent_rate _ room.chart
  apply ((((Bounded.const 2).mul a).add ((Bounded.const 2).mul b)).add old).of_le
  intro h i
  let c:=(p h i).chart
  have blocks : c.blocks≤2*c.blocks:=by omega
  have jobs:=Nat.mul_le_mul_right c.rows (Nat.mul_le_mul_right c.nodes blocks)
  have rows:=Nat.mul_le_mul_right c.rows blocks
  simp only [endAddress,out,scalarEnd,gateEnd,DescentDatedNodeMetadata.Chart.endAddress,
    DescentDatedNodeMetadata.Chart.output,DescentDatedNodeMetadata.Chart.scalarEnd,
    DescentDatedNodeMetadata.Chart.jobs,DescentDatedNodeMetadata.Chart.names,Nat.zero_add]
  dsimp only [c] at jobs rows
  omega

end Shape
end
end Hierarchy.DescentResetPrimitiveCheckpoint

end OAI
