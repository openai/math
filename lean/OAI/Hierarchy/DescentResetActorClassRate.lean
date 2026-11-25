import OAI.Hierarchy.DescentResetActorClassShape
import OAI.Hierarchy.DescentDatedOverlapAperture

namespace OAI
namespace Hierarchy.DescentResetActorClass.Shape
open DescentDatedAddressBook DescentSIMDLookup
variable {ι : ℕ→Type*} (c : ∀h,ι h→Shape)
theorem rate (raw : Bounded (fun h i=>(c h i).rawHosts)) (hosts : Bounded (fun h i=>(c h i).hosts))
    (groups : Bounded (fun h i=>(c h i).groups)) (lanes : Bounded (fun h i=>(c h i).lanes)) :
    Bounded (fun h i=>(c h i).endAddress 0):=by
  have pieces:Bounded (fun h i=>(c h i).parts):=(groups.add lanes).of_le fun _ _=>
    (Nat.div_le_self ..).trans (Nat.sub_le ..)
  exact ((Bounded.const 0).add (raw.mul pieces).padded).add
    (((Bounded.const 2).mul (hosts.mul pieces).padded).add raw.padded)
end Hierarchy.DescentResetActorClass.Shape

end OAI
