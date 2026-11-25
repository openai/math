import OAI.Hierarchy.DescentVenueShape
import OAI.Hierarchy.DescentDatedOverlapAperture

namespace OAI
/-! # Physical word extent of a lane-width conversion -/
namespace Hierarchy.DescentVenueSlabs
open DescentDatedAddressBook DescentSIMDLookup Filter
noncomputable section
variable {ι:ℕ→Type*}

theorem extent_rate (s:∀h,ι h→Shape)
    (sheets:Bounded (fun h i=>(s h i).pages)) (hosts:Bounded (fun h i=>(s h i).hosts))
    (groups:Bounded (fun h i=>(s h i).groups)) (old:Bounded (fun h i=>(s h i).sourceLanes))
    (next:Bounded (fun h i=>(s h i).targetLanes))
    (packed:∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(s h i).bits*(s h i).sourceLanes≤C*h) :
    Bounded (fun h i=>endAddress (s h i) 0) :=by
  have oldN:Bounded (fun h i=>chunks (s h i).groups (s h i).sourceLanes):=
    (groups.add old).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have nextN:Bounded (fun h i=>chunks (s h i).groups (s h i).targetLanes):=
    (groups.add next).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have copy:=(sheets.mul (hosts.mul oldN)).padded
  have exchange:=Overlap.address_rate (sheets.mul hosts) groups old next packed
  have last:=(hosts.mul nextN).padded
  apply ((copy.add exchange).add last).of_le
  intro h i
  rw [endAddress,Overlap.address_affine];simp [work,span]

end
end Hierarchy.DescentVenueSlabs

end OAI
