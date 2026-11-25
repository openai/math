import OAI.Hierarchy.DescentNextSignedAll
import OAI.Hierarchy.DescentOperandCandidatePages
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Actual public signed-token publication and normalized candidate result pages -/
namespace Hierarchy.DescentDatedAddressBook
open DescentNextSignedWindow.Native DescentSIMDLookup DescentOperandCandidateLookup Filter
noncomputable section

structure PublicOutput where
  blocks : ℕ
  capacity : ℕ
  signedBits : ℕ
  lanes : ℕ
  hosts : ℕ
  groups : ℕ
  candidates : ℕ
  queryBits : ℕ
  valueBits : ℕ
  fields : ℕ

namespace PublicOutput
variable (a : PublicOutput)
def rendered (base : ℕ) := All.endAddress base a.blocks a.capacity a.signedBits a.lanes a.hosts a.groups
def operands (base : ℕ) := dictionaryEnd (2*a.candidates) a.queryBits a.signedBits a.lanes (a.rendered base)
def endAddress (base : ℕ) := Batch.outputEnd a.fields a.hosts a.groups a.lanes (a.operands base)

theorem extent (base : ℕ) :
    a.endAddress base=base+(16+4*a.capacity)*2^((8*a.signedBits+a.signedBits)*a.lanes)+
      a.blocks*(2*a.capacity)*DescentDyadicSpan.span (a.hosts*chunks a.groups a.lanes)+
      ((2*a.candidates)*2)*2^((a.queryBits+a.signedBits)*a.lanes)+a.fields*(a.hosts*chunks a.groups a.lanes) := by
  simp only [endAddress,operands,rendered,Batch.outputEnd,dictionaryEnd,bits,All.end_address]

theorem translate (base : ℕ) : a.endAddress base=base+a.endAddress 0 := by
  rw [a.extent base,a.extent 0]
  omega

theorem occupied (base : ℕ) : base≤a.rendered base ∧ a.rendered base≤a.operands base ∧
    a.operands base≤a.endAddress base := by
  refine ⟨?_,Nat.le_add_right ..,Nat.le_add_right ..⟩
  unfold rendered
  rw [All.end_address]
  omega

variable {ι : ℕ→Type*}
theorem width_rate (p : ∀h,ι h→PublicOutput)
    (blocks : Bounded (fun h i=>(p h i).blocks)) (cap : Bounded (fun h i=>(p h i).capacity))
    (lanes : Bounded (fun h i=>(p h i).lanes)) (hosts : Bounded (fun h i=>(p h i).hosts))
    (groups : Bounded (fun h i=>(p h i).groups)) (candidates : Bounded (fun h i=>(p h i).candidates))
    (fields : Bounded (fun h i=>(p h i).fields))
    (pack : ∃K : ℕ,∀ᶠ h:ℕ in atTop,∀i,let v:=p h i;
      (8*v.signedBits+v.signedBits)*v.lanes≤K*h ∧ (v.queryBits+v.signedBits)*v.lanes≤K*h) :
    Bounded (fun h i=>(p h i).endAddress 0) := by
  obtain ⟨K,fit⟩:=pack
  have signed:=Bounded.pow_of_linear (K:=K) (fit.mono fun h hh i=>(hh i).1)
  have book:=Bounded.pow_of_linear (K:=K) (fit.mono fun h hh i=>(hh i).2)
  have batch : Bounded (fun h i=>chunks (p h i).groups (p h i).lanes) :=
    (groups.add lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows:=hosts.mul batch
  have rosters:=(((Bounded.const 16).add ((Bounded.const 4).mul cap)).mul signed).add
    ((blocks.mul ((Bounded.const 2).mul cap)).mul rows.padded)
  have all:=(rosters.add ((((Bounded.const 2).mul candidates).mul (Bounded.const 2)).mul book)).add (fields.mul rows)
  apply all.of_le
  intro h i
  rw [(p h i).extent]
  simp only [Nat.zero_add,DescentDyadicSpan.span,Nat.le_refl]

end PublicOutput
end
end Hierarchy.DescentDatedAddressBook

end OAI
