import OAI.Hierarchy.DescentContactOutputShape
import OAI.Hierarchy.DescentContactMaskRate
import OAI.Hierarchy.DescentResetStemProjectRate

namespace OAI
/-! # True address roof for selected contact operands at the next block and lane pitch -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentDatedAddressBook DescentSIMDLookup Filter
variable {ι : ℕ→Type*} (p : ∀h,ι h→Shape)
structure ScalarRoom : Prop where
  donor : DescentContactDonorFront.Shape.ScalarRoom (fun h i => (p h i).donor)
  sockets : Bounded (fun h i=>(p h i).sockets)
  shapes : Bounded (fun h i=>(p h i).shapes)
  groups : Bounded (fun h i=>(p h i).groups)
  blocks : Bounded (fun h i=>(p h i).blocks)
  batch : Bounded (fun h i=>(p h i).batch)
  key : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let a:=p h i
    a.markerBits*a.donor.batch≤K*h ∧ a.metaBits*a.donor.batch≤K*h ∧ (a.metaBits*a.blocks)*a.batch≤K*h

theorem rate (r : ScalarRoom p) : Bounded (fun h i=>(p h i).endAddress 0):=by
  let c (n : ℕ):=Bounded.const (ι:=ι) n
  obtain ⟨K,yes⟩:=r.key
  obtain ⟨J,oldKeys⟩:=r.donor.keys
  have measured := DescentContactMaskShape.rate (fun h i => (p h i).donor) r.donor r.sockets
  have marker:=Bounded.pow_of_linear (K:=K) (yes.mono fun h g i=>(g i).1)
  have «meta»:=Bounded.pow_of_linear (K:=K) (yes.mono fun h g i=>(g i).2.1)
  have field:=Bounded.pow_of_linear (K:=J) (oldKeys.mono fun h g i=>(g i).2.2.2.1)
  have cargo:=Bounded.pow_of_linear (K:=J) (oldKeys.mono fun h g i=>(g i).2.2.2.2.2.2.1)
  have select : Bounded (fun h i=>2^(p h i).choiceBits):=by
    apply Bounded.pow_of_linear (K:=J+2*K)
    filter_upwards [yes,oldKeys] with h a b
    intro i
    have m:=(a i).2.1
    have f:=(b i).2.2.2.1
    simp only [choiceBits,Nat.add_mul,Nat.mul_assoc 2 K h,max_le_iff]
    constructor <;> omega
  have before:=((((measured.add ((c 2).mul marker)).add ((c 2).mul marker)).add ((c 2).mul field)).add ((c 2).mul cargo)).add
    (((r.sockets.add (c 1)).mul (c 2)).mul select)
  have projection:=DescentResetStemProject.rates (a := fun h i => (p h i).metaBits)
    (r.sockets.mul (c 4)) (r.donor.hosts.mul r.shapes)
    r.groups r.blocks r.donor.batch r.batch ⟨K,yes.mono (fun h g i=>(g i).2.1)⟩
      ⟨K,yes.mono (fun h g i=>(g i).2.2)⟩
  apply (before.add projection).of_le
  intro h i
  rw [endAddress,DescentResetStemProject.extent]; exact le_rfl

end Hierarchy.DescentContactOutputShape.Shape

end OAI
