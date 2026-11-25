import OAI.Hierarchy.DescentContactDonorShape
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # The one acquired contact sender and old-halo calendar has word-sized addresses -/
namespace Hierarchy.DescentContactDonorFront.Shape
open DescentDatedAddressBook DescentSIMDLookup Filter
noncomputable section
variable {ι : ℕ→Type*} (p : ∀h,ι h→Shape)

structure ScalarRoom : Prop where
  hosts : Bounded (fun h i=>(p h i).hosts)
  groups : Bounded (fun h i=>(p h i).groups)
  batch : Bounded (fun h i=>(p h i).batch)
  degree : Bounded (fun h i=>(p h i).degree)
  lows : Bounded (fun h i=>(p h i).lows)
  cap : Bounded (fun h i=>(p h i).cap)
  oldArity : Bounded (fun h i=>(p h i).boardFields)
  oppositeArity : Bounded (fun h i=>(p h i).returnFields)
  keys : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let v:=p h i;let b:=v.fieldBits;let M:=v.batch
    let N:=v.boardFields
    let F:=v.laneFields
    let R:=v.returnFields
    (b*N+b)*M≤K*h ∧ ((b*F)*2+b*F)*M≤K*h ∧ (b*R+b)*M≤K*h ∧ b*M≤K*h ∧
      v.queryBits*M≤K*h ∧ v.queryBits*M+v.cargoBits≤K*h ∧ v.cargoBits*M≤K*h ∧
      (v.cargoBits+v.cargoBits)*M≤K*h

private theorem dictionary {key row : ∀h,ι h→ℕ}
    (a : Bounded (fun h i=>2^(key h i))) (b : Bounded (fun h i=>2^(row h i))) :
    Bounded (fun h i=>2^(max (key h i) (row h i))) :=by
  apply (a.max' b).of_le
  intro h i
  rcases le_total (key h i) (row h i) with l|g
  · rw [max_eq_right l];exact le_max_right ..
  · rw [max_eq_left g];exact le_max_left ..

theorem rate (r : ScalarRoom p) : Bounded (fun h i=>(p h i).endAddress 0) :=by
  let c (n:ℕ):=Bounded.const (ι:=ι) n
  obtain ⟨K,hk⟩:=r.keys
  have keys1:=Bounded.pow_of_linear (K:=K) (hk.mono fun h w i=>(w i).1)
  have keys2:=Bounded.pow_of_linear (K:=K) (hk.mono fun h w i=>(w i).2.1)
  have keys3:=Bounded.pow_of_linear (K:=K) (hk.mono fun h w i=>(w i).2.2.1)
  have f:=Bounded.pow_of_linear (K:=K) (hk.mono fun h w i=>(w i).2.2.2.1)
  have q:=Bounded.pow_of_linear (K:=K) (hk.mono fun h w i=>(w i).2.2.2.2.1)
  have qb:=Bounded.pow_of_linear (K:=K) (hk.mono fun h w i=>(w i).2.2.2.2.2.1)
  have b:=Bounded.pow_of_linear (K:=K) (hk.mono fun h w i=>(w i).2.2.2.2.2.2.1)
  have bb:=Bounded.pow_of_linear (K:=K) (hk.mono fun h w i=>(w i).2.2.2.2.2.2.2)
  have chunks_ : Bounded (fun h i=>chunks (p h i).groups (p h i).batch) :=
    (r.groups.add r.batch).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows:=r.hosts.mul chunks_
  have lanes:=((c 2).mul ((r.lows.mul ((c 2).mul r.cap)).mul (c 3)))
  have jobs:=(r.lows.mul ((c 2).mul r.cap)).mul (c 2)
  have small:=rows.padded
  have table1:=((r.oldArity.mul (c 2)).add (c 2)).mul (dictionary keys1 small)
  have end1:=(((c 0).add table1).add small).add ((c 1).mul small)
  have table2:=(c (2*2+2)).mul (dictionary keys2 small)
  have split:=((((end1.add (lanes.mul small)).add table2).add small).add (lanes.mul small))
  have table3:=((r.oppositeArity.mul (c 2)).add (c 2)).mul (dictionary keys3 small)
  have twice:=(((split.add table3).add small).add (jobs.mul small))
  have recovered:=((twice.add table3).add small).add (jobs.mul small)
  have before:=recovered.add ((c 1).add r.hosts.padded)
  have d:=r.degree.add (c 1)
  have look:=q.add ((d.mul qb).add (b.add (bb.add rows)))
  have cells:=((((c 3).mul (r.hosts.mul d).padded).add ((c 2).mul f)).add look).add (rows.add (c 1)).padded
  exact before.add cells

end
end Hierarchy.DescentContactDonorFront.Shape

end OAI
