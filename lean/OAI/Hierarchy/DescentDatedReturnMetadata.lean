import OAI.Hierarchy.DescentDatedNodeMetadataRate

namespace OAI
/-! # Occupancy and arity read both the current funded count and the retained argument spans -/
namespace Hierarchy.DescentDatedAddressBook
open Filter
noncomputable section
structure MetadataReturn where
  chart : DescentDatedNodeMetadata.Chart
  paidBits : ℕ
  spanBits : ℕ
namespace MetadataReturn
variable (v : MetadataReturn)

def headerEnd (base : ℕ) :=base+(v.chart.nodes+1)*(2*2^(max v.paidBits (v.spanBits+v.chart.bits)*v.chart.lanes))
def endAddress (base : ℕ) :=v.chart.endAddress (v.headerEnd base)
def unpackEnd (base : ℕ) :=base+v.chart.nodes*2^((v.spanBits*v.chart.nodes)*v.chart.lanes)
def ordinaryEnd (base : ℕ) :=v.endAddress (v.unpackEnd base)

theorem translate (base : ℕ) : v.endAddress base=base+v.endAddress 0 :=by
  change v.chart.endAddress (v.headerEnd base)=base+v.chart.endAddress (v.headerEnd 0)
  rw [v.chart.translate (v.headerEnd base),v.chart.translate (v.headerEnd 0)]
  simp only [headerEnd,Nat.zero_add,Nat.add_assoc]
theorem ordinary_translate (base : ℕ) : v.ordinaryEnd base=base+v.ordinaryEnd 0 :=by
  change v.endAddress (v.unpackEnd base)=base+v.endAddress (v.unpackEnd 0)
  rw [v.translate (v.unpackEnd base),v.translate (v.unpackEnd 0)]
  simp only [unpackEnd,Nat.zero_add,Nat.add_assoc]

variable {ι : ℕ→Type*} (p : ∀h,ι h→MetadataReturn)
structure ScalarRoom : Prop where
  chart : DescentDatedNodeMetadata.Chart.ScalarRoom (fun h i=>(p h i).chart)
  header : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let v:=p h i;max v.paidBits (v.spanBits+v.chart.bits)*v.chart.lanes≤K*h

theorem extent_rate (r : ScalarRoom p) : Bounded (fun h i=>(p h i).endAddress 0) :=by
  obtain ⟨K,hk⟩:=r.header
  have head:=(r.chart.nodes.add (Bounded.const 1)).mul ((Bounded.const 2).mul (Bounded.pow_of_linear (K:=K) hk))
  have old:=DescentDatedNodeMetadata.Chart.extent_rate _ r.chart
  apply (head.add old).of_le
  intro h i
  rw [endAddress,(p h i).chart.translate]
  simp [headerEnd]

theorem ordinary_rate (r : ScalarRoom p)
    (digits : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let v:=p h i;(v.spanBits*v.chart.nodes)*v.chart.lanes≤K*h) :
    Bounded (fun h i=>(p h i).ordinaryEnd 0) :=by
  obtain ⟨K,hk⟩:=digits
  have page:=r.chart.nodes.mul (Bounded.pow_of_linear (K:=K) hk)
  apply (page.add (extent_rate p r)).of_le
  intro h i
  rw [ordinaryEnd,(p h i).translate]
  simp [unpackEnd]

end MetadataReturn
end
end Hierarchy.DescentDatedAddressBook

end OAI
