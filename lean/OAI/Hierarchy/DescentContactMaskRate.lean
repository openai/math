import OAI.Hierarchy.DescentContactMaskShape
import OAI.Hierarchy.DescentContactDonorFrontRate

namespace OAI
/-! # Address rate for the original positive contact mass held after the trunk date -/
namespace Hierarchy.DescentContactMaskShape
open DescentDatedAddressBook DescentSIMDLookup Filter
variable {ι : ℕ→Type*} (p : ∀h,ι h→DescentContactDonorFront.Shape)

theorem rate (r : DescentContactDonorFront.Shape.ScalarRoom p) (q : Bounded (fun h i=>sockets (p h i))) :
    Bounded (fun h i=>endAddress (p h i) 0):=by
  let c (n : ℕ):=Bounded.const (ι:=ι) n
  have rows : Bounded (fun h i=>(p h i).hosts*chunks (p h i).groups (p h i).batch):=
    r.hosts.mul ((r.groups.add r.batch).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..))
  have pad:=rows.padded
  have inputs : Bounded (fun h i=>donors (p h i)+1):=r.oldArity.of_le (fun _ _=>donor_arity _)
  obtain ⟨K,hk⟩:=r.keys
  have keys : Bounded (fun h i=>2^(((p h i).fieldBits*(donors (p h i)+1)+(p h i).fieldBits)*(p h i).batch)):=by
    apply Bounded.pow_of_linear (K:=K)
    filter_upwards [hk] with h yes
    intro i
    apply le_trans _ (yes i).1
    gcongr
    exact donor_arity _
  have paddedKeys : Bounded (fun h i=>2^(max (((p h i).fieldBits*(donors (p h i)+1)+(p h i).fieldBits)*(p h i).batch)
      (Nat.clog 2 ((p h i).hosts*chunks (p h i).groups (p h i).batch)))):=by
    apply (keys.max' pad).of_le
    intro h i
    rcases le_total (((p h i).fieldBits*(donors (p h i)+1)+(p h i).fieldBits)*(p h i).batch)
      (Nat.clog 2 ((p h i).hosts*chunks (p h i).groups (p h i).batch)) with l|g
    · rw [max_eq_right l];exact le_max_right ..
    · rw [max_eq_left g];exact le_max_left ..
  have signSize : Bounded (fun h i=>2^((p h i).fieldBits*(p h i).batch)):=
    Bounded.pow_of_linear (K:=K) (hk.mono fun h good i=>(good i).2.2.2.1)
  exact (((((c 0).add (q.mul pad)).add (((inputs.mul (c 2)).add (c 2)).mul paddedKeys)).add pad).add (q.mul pad)).add ((c 2).mul signSize)

end Hierarchy.DescentContactMaskShape

end OAI
