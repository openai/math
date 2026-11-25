import OAI.Hierarchy.DescentContactMaskShape
import OAI.Hierarchy.DescentResetStemProject

namespace OAI
/-! # Direct contact fields through old-halo selection and genuine new block/pitch projection -/
namespace Hierarchy.DescentContactOutputShape
open DescentSIMDLookup
structure Shape where
  donor : DescentContactDonorFront.Shape
  shapes : ℕ
  groups : ℕ
  blocks : ℕ
  batch : ℕ
  markerBits : ℕ
  metaBits : ℕ
namespace Shape
variable (A : Shape)
def sockets := DescentContactMaskShape.sockets A.donor
def fields := A.sockets*4
def sparseHosts := A.donor.hosts*A.shapes
def marker (base : ℕ):=DescentContactMaskShape.endAddress A.donor base
def flagPage (base : ℕ):=A.marker base+2*2^(A.markerBits*A.donor.batch)
def countPage (base : ℕ):=A.flagPage base+2*2^(A.markerBits*A.donor.batch)
def haloPage (base : ℕ):=A.countPage base+2*2^(A.donor.fieldBits*A.donor.batch)
def choicePage (base : ℕ):=A.haloPage base+2*2^(A.donor.cargoBits*A.donor.batch)
def choiceBits:=max ((A.donor.fieldBits+A.metaBits)*A.donor.batch) ((A.metaBits+A.metaBits)*A.donor.batch)
def projected (base : ℕ):=A.choicePage base+(A.sockets+1)*2*2^A.choiceBits
def endAddress (base : ℕ):=DescentResetStemProject.endAddress (A.projected base) A.fields A.sparseHosts A.groups
  A.blocks A.metaBits A.donor.batch A.batch
theorem relative (base : ℕ) : A.projected base=base+A.projected 0:=by
  simp only [projected,choicePage,haloPage,countPage,flagPage,marker,DescentContactMaskShape.translate A.donor base,Nat.add_assoc]
theorem translate (base : ℕ) : A.endAddress base=base+A.endAddress 0:=by
  rw [endAddress,DescentResetStemProject.extent,A.relative]
  change (base+A.projected 0)+_=base+DescentResetStemProject.endAddress _ _ _ _ _ _ _ _
  rw [DescentResetStemProject.extent (A.projected 0),Nat.add_assoc]
theorem cuts (base : ℕ) : base≤A.marker base ∧ A.marker base≤A.countPage base ∧ A.countPage base≤A.haloPage base ∧
    A.haloPage base≤A.choicePage base ∧ A.choicePage base≤A.projected base ∧ A.projected base≤A.endAddress base :=
  ⟨DescentContactMaskShape.prior _ _,(Nat.le_add_right ..).trans (Nat.le_add_right ..),Nat.le_add_right ..,Nat.le_add_right ..,
    Nat.le_add_right ..,by unfold endAddress;rw [DescentResetStemProject.extent];exact Nat.le_add_right ..⟩
end Shape
end Hierarchy.DescentContactOutputShape

end OAI
