import OAI.Hierarchy.DescentDatedRetainedSetupRate
import OAI.Hierarchy.DescentDatedRetainedPlacementRate

namespace OAI
/-! # Independent old-role transfer at the preceding primitive register width -/
namespace Hierarchy.DescentRetainedPrimitive
open DescentDatedAddressBook DescentSIMDLookup DescentGLPacked.BankImage DescentGLControlCode Filter
noncomputable section
structure Layout where
  transfer : DescentResetRetainedSetup.Layout
  newHosts : ℕ
  shapes : ℕ
  groups : ℕ
  blocks : ℕ
  lanes : ℕ
namespace Layout
variable (z : Layout)
def placement : DescentResetRetainedPlacement.Chart :=
  ⟨z.transfer.hosts,z.newHosts,z.shapes,z.groups,z.blocks,z.lanes⟩
def batch : DescentResetRetainedPlacement.Batch := ⟨z.transfer.nodes,z.transfer.bits,z.transfer.decodedLanes⟩
def bookWords :=let v:=z.transfer;(v.channels+v.nodes)*(2*2^((v.stripWord*v.channels+v.stripWord)*v.decodedLanes))
def placementBase (floor : ℕ) :=z.transfer.tables floor+z.bookWords
def endAddress (floor : ℕ) :=z.placement.endAddress z.batch (z.placementBase floor)
def bank (floor : ℕ) (n : Fin z.transfer.nodes) (x : Fin z.blocks) :=z.placement.bank z.batch (z.placementBase floor) n x

theorem translate (floor : ℕ) : z.endAddress floor=floor+z.endAddress 0:=by
  unfold endAddress
  rw [z.placement.affine z.batch (z.placementBase floor),z.placement.affine z.batch (z.placementBase 0)]
  simp only [placementBase,DescentResetRetainedSetup.Layout.tables,DescentResetRetainedSetup.Layout.mixed,
    SignedFields.stop,Dated.extent,DescentResetRetainedSetup.Layout.matrix,DescentResetRetainedSetup.Layout.slots,
    DescentResetRetainedSetup.Layout.digits,Nat.zero_add,Nat.add_assoc]

variable {ι : ℕ→Type*} (p : ∀h,ι h→Layout)
structure ScalarRoom : Prop where
  transfer : DescentResetRetainedSetup.Layout.ScalarRoom (fun h i=>(p h i).transfer)
  placement : DescentResetRetainedPlacement.Chart.ScalarRoom (fun h i=>(p h i).placement) (fun h i=>(p h i).batch)

theorem rate (r : ScalarRoom p) : Bounded (fun h i=>(p h i).endAddress 0):=by
  have before:=(DescentResetRetainedSetup.Layout.extent_rate _ r.transfer).of_le
    (y:=fun h i=>(p h i).transfer.tables 0) (fun h i=>by
      obtain ⟨_,_,_,_,_,h₁,h₂,h₃,h₄⟩:=(p h i).transfer.order 0
      exact h₁.trans (h₂.trans (h₃.trans h₄)))
  have slots:=((Bounded.const 2).add ((Bounded.const 7).mul r.transfer.oldArgs)).mul r.transfer.oldNodes
  obtain ⟨K,bounds⟩:=r.transfer.packed
  have lookup:=Bounded.pow_of_linear (K:=K) (bounds.mono (fun h b i=>(b i).2.2.2.2.2.2.1))
  have dict : Bounded (fun h i=>(p h i).bookWords):=(slots.add r.transfer.nodes).mul ((Bounded.const 2).mul lookup)
  have aft:=DescentResetRetainedPlacement.Chart.extent_rate _ _ r.placement
  apply ((before.add dict).add aft).of_le
  intro h i
  rw [endAddress,(p h i).placement.affine (p h i).batch]
  exact le_rfl
end Layout
end
end Hierarchy.DescentRetainedPrimitive

end OAI
