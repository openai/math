import OAI.Hierarchy.DescentRetainedControlLayout
import OAI.Hierarchy.DescentDatedRetainedTargetRate
import OAI.Hierarchy.DescentDatedRetainedSetupRate
import OAI.Hierarchy.DescentRetainedSevenChart

namespace OAI
/-! # Space of the saved argument stream after testing donor ownership and restoring its order -/
namespace Hierarchy.DescentRetainedSeven.Chart
open DescentDatedAddressBook Filter
noncomputable section
variable {ι : ℕ→Type*} (v : ∀h,ι h→DescentRetainedSeven.Chart)

theorem extent_rate (old : DescentResetRetainedSetup.Layout.ScalarRoom (fun h i=>(v h i).retained))
    (selected : DescentRetainedControl.Layout.ScalarRoom (fun h i=>(v h i).control))
    (out : DescentResetRetainedPlacement.Chart.ScalarRoom (fun h i=>(v h i).placement) (fun h i=>(v h i).batch)) :
    Bounded (fun h i=>(v h i).endAddress 0) :=by
  let c j:=Bounded.const (ι:=ι) j
  have start : Bounded (fun h i=>(v h i).seen 0):=by
    apply (DescentResetRetainedSetup.Layout.extent_rate _ old).of_le
    intro h i
    obtain ⟨_,_,_,_,_,h₁,h₂,h₃,h₄⟩:=(v h i).retained.order 0
    exact h₁.trans (h₂.trans (h₃.trans h₄))
  have tab : Bounded (fun h i=>(v h i).tabs 0):=by
    apply (start.add (DescentRetainedControl.Layout.rate _ selected)).of_le
    intro h i
    exact ((v h i).control.translate _).le
  obtain ⟨K,cost⟩:=old.packed
  have book:=Bounded.pow_of_linear (K:=K) (cost.mono fun h w i=>(w i).2.2.2.2.2.2.1)
  have last : Bounded (fun h i=>let r:=(v h i).retained;2^(r.siteWord*r.decodedLanes)):=by
    apply book.of_le
    intro h i
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_add_right ..))
  have channels:=((c 2).add ((c 7).mul old.oldArgs)).mul old.oldNodes
  have loc:=((tab.add ((channels.add (c 1)).mul book)).add (out.fields.mul last))
  apply (loc.add (DescentRetainedTargetPlacement.Chart.extent_rate _ _ out)).of_le
  intro h i
  exact (DescentRetainedTargetPlacement.Chart.affine _ _ _).le

end
end Hierarchy.DescentRetainedSeven.Chart

end OAI
