import OAI.Hierarchy.DescentResetRetainedChart
import OAI.Hierarchy.DescentRetainedControlChart
import OAI.Hierarchy.DescentDatedRetainedPlacementRate
import OAI.Hierarchy.DescentRotorWindowArchive
import OAI.Hierarchy.DescentResetRetileStrip

namespace OAI
/-! # Address chart for the original-window donor selection and its two genuine pitches -/
namespace Hierarchy.DescentRetainedControl
open DescentSIMDLookup DescentDatedAddressBook Filter
noncomputable section
namespace Layout
variable (s : Layout)
def control (base : ℕ) (j : Fin s.targets) :=DescentResetRetainedSetup.Strip.bank (s.temporary base) s.hosts s.groups s.oldLanes s.lanes s.selectorBits j.val

variable {ι : ℕ→Type*} (p : ∀h,ι h→Layout)
structure ScalarRoom : Prop where
  hosts : Bounded (fun h i=>(p h i).hosts)
  groups : Bounded (fun h i=>(p h i).groups)
  targets : Bounded (fun h i=>(p h i).targets)
  before : Bounded (fun h i=>(p h i).oldLanes)
  after_ : Bounded (fun h i=>(p h i).lanes)
  packed : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,max ((p h i).rootWidth*(p h i).oldLanes)
    (max ((p h i).selectorBits*(p h i).oldLanes) ((p h i).aperture*(p h i).lanes))≤K*h

theorem rate (r : ScalarRoom p) : Bounded (fun h i=>(p h i).endAddress 0):=by
  obtain ⟨K,wide⟩:=r.packed
  have before:=wide.mono (fun h ok i=>(Nat.le_max_left ..).trans (ok i))
  have sel:=wide.mono (fun h ok i=>((Nat.le_max_left ..).trans (Nat.le_max_right ..)).trans (ok i))
  have after_:=wide.mono (fun h ok i=>((Nat.le_max_right ..).trans (Nat.le_max_right ..)).trans (ok i))
  have rows : Bounded (fun h i => (p h i).rows) := r.hosts.mul ((r.groups.add r.before).of_le (fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)))
  have gate₁:=r.targets.mul ((Bounded.const 2).mul (Bounded.pow_of_linear (K:=K) before))
  have gate₂:=((Bounded.const 2).mul r.targets).mul ((Bounded.const 2).mul (Bounded.pow_of_linear (K:=K) after_))
  have regrid:=Overlap.address_rate r.hosts r.groups r.before r.after_ ⟨K,sel⟩
  exact ((((gate₁.add (r.targets.mul rows)).add rows.padded).add (r.targets.mul regrid)).add gate₂).of_le
    fun _ _=>by simp only [endAddress,received,temporary,installed,Nat.zero_add];exact le_rfl
end Layout
end
end Hierarchy.DescentRetainedControl

end OAI
