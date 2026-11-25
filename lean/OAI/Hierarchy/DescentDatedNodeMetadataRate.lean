import OAI.Hierarchy.DescentDatedNodeMetadataChart
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Public scalar bounds on the node metadata checkpoint -/
namespace Hierarchy.DescentDatedNodeMetadata.Chart
open DescentDatedAddressBook DescentSIMDLookup Filter
variable {ι : ℕ→Type*}
structure ScalarRoom (v : ∀h,ι h→DescentDatedNodeMetadata.Chart) where
  blocks : Bounded (fun h i=>(v h i).blocks)
  nodes : Bounded (fun h i=>(v h i).nodes)
  hosts : Bounded (fun h i=>(v h i).hosts)
  groups : Bounded (fun h i=>(v h i).groups)
  lanes : Bounded (fun h i=>(v h i).lanes)
  width : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let a:=v h i;(a.bits*a.nodes+a.bits)*a.lanes≤K*h

theorem seed_rate (v : ∀h,ι h→DescentDatedNodeMetadata.Chart) (room : ScalarRoom v) :
    Bounded (fun h i=>(v h i).seedEnd 0) :=by
  have count : Bounded (fun h i=>(v h i).names):=(Bounded.const 2).mul room.blocks
  have parts : Bounded (fun h i=>chunks (v h i).groups (v h i).lanes):=
    (room.groups.add room.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have r : Bounded (fun h i=>(v h i).rows):=room.hosts.mul parts
  have page : Bounded (fun h i=>(v h i).rounded):=(r.add (Bounded.const 1)).padded
  simpa only [seedEnd,Nat.zero_add] using (count.mul r).add page

theorem extent_rate (v : ∀h,ι h→DescentDatedNodeMetadata.Chart) (room : ScalarRoom v) :
    Bounded (fun h i=>(v h i).endAddress 0) :=by
  have count : Bounded (fun h i=>(v h i).names):=(Bounded.const 2).mul room.blocks
  have parts : Bounded (fun h i=>chunks (v h i).groups (v h i).lanes):=
    (room.groups.add room.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have r : Bounded (fun h i=>(v h i).rows):=room.hosts.mul parts
  have page : Bounded (fun h i=>(v h i).rounded):=(r.add (Bounded.const 1)).padded
  obtain ⟨K,sizes⟩:=room.width
  have dict : Bounded (fun h i=>(v h i).dictionary):=(room.nodes.add (Bounded.const 1)).mul (Bounded.pow_of_linear sizes)
  simpa only [endAddress,output,scalarEnd,jobs,Nat.zero_add] using
    (((((count.mul room.nodes).mul r).add (dict.max' page)).add (count.mul r)).add page)

end Hierarchy.DescentDatedNodeMetadata.Chart

end OAI
