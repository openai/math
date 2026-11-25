import OAI.Hierarchy.DescentDatedOverlapAperture

namespace OAI
/-! # Repack the retained ordinary profile before staging the current matcher -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSIMDLookup Filter
noncomputable section
structure ProfileRepack where
  seats : ℕ
  oldLanes : ℕ
  newLanes : ℕ
  bits : ℕ
namespace ProfileRepack
variable (p : ProfileRepack)
/-- The overlap code returns the new pitch, after which the scalar profile widening
dictionary occupies a single page at the new pitch. -/
def endAddress (base : ℕ) :=Overlap.endAddress base 1 p.seats p.oldLanes p.newLanes p.bits+2^(p.bits*p.newLanes)
theorem translate (base : ℕ) : p.endAddress base=base+p.endAddress 0 :=by
  rw [endAddress,endAddress,Overlap.address_affine]
  omega

variable {ι : ℕ→Type*} (p : ∀h,ι h→ProfileRepack)
structure ScalarRoom : Prop where
  seats : Bounded (fun h i=>(p h i).seats)
  original : Bounded (fun h i=>(p h i).oldLanes)
  next : Bounded (fun h i=>(p h i).newLanes)
  oldKey : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(p h i).bits*(p h i).oldLanes≤K*h
  newKey : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(p h i).bits*(p h i).newLanes≤K*h
theorem extent_rate (b : ScalarRoom p) : Bounded (fun h i=>(p h i).endAddress 0) :=by
  obtain ⟨K,hk⟩:=b.newKey
  exact (Overlap.address_rate (Bounded.const 1) b.seats b.original b.next b.oldKey).add
    (Bounded.pow_of_linear (K:=K) hk)
end ProfileRepack
end
end Hierarchy.DescentDatedAddressBook

end OAI
