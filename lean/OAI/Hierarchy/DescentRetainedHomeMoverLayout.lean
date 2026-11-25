import OAI.Hierarchy.DescentPrimitiveMoverLayout
import OAI.Hierarchy.DescentRetainedControlLayout
import OAI.Hierarchy.DescentDatedRetainedTargetRate

namespace OAI
/-! # Address diagram of the ordered per-home primitive handoff -/
namespace Hierarchy.DescentRetainedHomeMover
open DescentDatedAddressBook DescentSIMDLookup DescentGLPacked.BankImage DescentGLControlCode Filter
noncomputable section
structure Layout extends DescentRetainedPrimitive.Layout where
  degree : ℕ
  cap : ℕ
  rootField : ℕ
  rootLanes : ℕ

namespace Layout
variable (z : Layout)
abbrev placement:=z.toLayout.placement
abbrev batch:=z.toLayout.batch
def control : DescentRetainedControl.Layout :=
  ⟨z.transfer.hosts,z.transfer.grouped,z.shapes,z.transfer.donors,z.degree,z.cap,
   z.rootField,z.transfer.bits,z.rootLanes,z.transfer.decodedLanes⟩
def controlBase (floor : ℕ):=z.transfer.tables floor
def bookBase (floor : ℕ):=z.control.endAddress (z.controlBase floor)
def placementBase (floor : ℕ):=z.bookBase floor+z.toLayout.bookWords
def endAddress (floor : ℕ):=DescentRetainedTargetPlacement.Chart.endAddress z.placement z.batch (z.placementBase floor)
def bank (floor : ℕ) (n : Fin z.transfer.nodes) (x : Fin z.blocks) :=
  DescentRetainedTargetPlacement.Chart.bank z.placement z.batch (z.placementBase floor) n x

theorem translate (floor : ℕ) : z.endAddress floor=floor+z.endAddress 0:=by
  unfold endAddress
  rw [DescentRetainedTargetPlacement.Chart.affine z.placement z.batch (z.placementBase floor),
    DescentRetainedTargetPlacement.Chart.affine z.placement z.batch (z.placementBase 0)]
  simp only [placementBase,bookBase]
  rw [z.control.translate (z.controlBase floor),z.control.translate (z.controlBase 0)]
  simp only [controlBase,DescentResetRetainedSetup.Layout.tables,DescentResetRetainedSetup.Layout.mixed,
    SignedFields.stop,Dated.extent,DescentResetRetainedSetup.Layout.matrix,DescentResetRetainedSetup.Layout.slots,
    DescentResetRetainedSetup.Layout.digits,Nat.zero_add,Nat.add_assoc]

variable {ι : ℕ→Type*} (p : ∀h,ι h→Layout)
structure ScalarRoom : Prop where
  transfer : DescentResetRetainedSetup.Layout.ScalarRoom (fun h i=>(p h i).transfer)
  control : DescentRetainedControl.Layout.ScalarRoom (fun h i=>(p h i).control)
  placement : DescentResetRetainedPlacement.Chart.ScalarRoom (fun h i=>(p h i).placement) (fun h i=>(p h i).batch)

theorem rate (r : ScalarRoom p) : Bounded (fun h i=>(p h i).endAddress 0):=by
  have before:=(DescentResetRetainedSetup.Layout.extent_rate _ r.transfer).of_le
    (y:=fun h i=>(p h i).transfer.tables 0) (fun h i=>by
      obtain ⟨_,_,_,_,_,h₁,h₂,h₃,h₄⟩:=(p h i).transfer.order 0
      exact h₁.trans (h₂.trans (h₃.trans h₄)))
  have slots:=((Bounded.const 2).add ((Bounded.const 7).mul r.transfer.oldArgs)).mul r.transfer.oldNodes
  obtain ⟨K,bounds⟩:=r.transfer.packed
  have lookup:=Bounded.pow_of_linear (K:=K) (bounds.mono (fun h b i=>(b i).2.2.2.2.2.2.1))
  have dict : Bounded (fun h i=>(p h i).toLayout.bookWords):=(slots.add r.transfer.nodes).mul ((Bounded.const 2).mul lookup)
  have routing:=DescentRetainedControl.Layout.rate _ r.control
  have aft:=DescentRetainedTargetPlacement.Chart.extent_rate _ _ r.placement
  apply (((before.add routing).add dict).add aft).of_le
  intro h i
  rw [endAddress,DescentRetainedTargetPlacement.Chart.affine,placementBase,bookBase,(p h i).control.translate]
  exact le_rfl

end Layout
end
end Hierarchy.DescentRetainedHomeMover

end OAI
