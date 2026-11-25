import OAI.Hierarchy.DescentFundedCensusLayout
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Address bound for every shape's funded reset columns -/
namespace Hierarchy.DescentFundedCensus.Shape
open DescentDatedAddressBook DescentSIMDLookup Filter
noncomputable section
variable {ι : ℕ→Type*} (s : ∀h,ι h→DescentFundedCensus.Shape)

structure ScalarRoom : Prop where
  jobs : Bounded (fun h i=>(s h i).jobs)
  hosts : Bounded (fun h i=>(s h i).hosts)
  groups : Bounded (fun h i=>(s h i).groups)
  lanes : Bounded (fun h i=>(s h i).lanes)
  lookup : ∃A : ℕ,∀ᶠ h : ℕ in atTop,∀i,(s h i).broadcast*(s h i).lanes≤A*h

theorem rate (r : ScalarRoom s) : Bounded (fun h i=>(s h i).roof 0) := by
  obtain ⟨A,hw⟩:=r.lookup
  have offsets : Bounded (fun h i=>2^(s h i).width) := Bounded.pow_of_linear (K:=A) hw
  have chunksBound : Bounded (fun h i=>chunks (s h i).groups (s h i).lanes) :=
    (r.groups.add r.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have written:=(r.jobs.mul (r.hosts.mul chunksBound))
  have forms:=((Bounded.const (ι:=ι) 2).mul (r.jobs.add (Bounded.const 1))).mul offsets
  exact ((Bounded.const 0).add forms).add written.padded

end
end Hierarchy.DescentFundedCensus.Shape

end OAI
