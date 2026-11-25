import OAI.Hierarchy.DescentPrivateMaskShape
import OAI.Hierarchy.DescentResetStemProjectRate

namespace OAI
/-! # Space for the extracted private raw fields and the successor block rotation -/
namespace Hierarchy.DescentPrivateMaskDeck.Shape
open DescentDatedAddressBook Filter
variable {ι : ℕ→Type*} (p : ∀h,ι h→Hierarchy.DescentPrivateMaskDeck.Shape)
structure ScalarRoom : Prop where
  oldHosts : Bounded fun h i=>(p h i).oldHosts
  shapes : Bounded fun h i=>(p h i).shapes
  groups : Bounded fun h i=>(p h i).groups
  blocks : Bounded fun h i=>(p h i).blocks
  oldBatch : Bounded fun h i=>(p h i).oldBatch
  batch : Bounded fun h i=>(p h i).batch
  cap : Bounded fun h i=>(p h i).cap
  keys : Bounded fun h i=>(p h i).keys
  raw : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(p h i).panels*(p h i).oldBatch≤K*h
  «meta» : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(p h i).metaBits*(p h i).oldBatch≤K*h
  projected : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,((p h i).metaBits*(p h i).blocks)*(p h i).batch≤K*h

theorem rate (r : ScalarRoom p) : Bounded fun h i=>(p h i).endAddress 0 := by
  obtain ⟨K,hK⟩:=r.raw
  have words:=Bounded.pow_of_linear (K:=K) hK
  have three:=Bounded.const (ι:=ι) 3
  have «prefix»:=(r.cap.mul three).mul words
  have projection:=DescentResetStemProject.rates (r.keys.mul three) (r.oldHosts.mul r.shapes) r.groups r.blocks
    r.oldBatch r.batch r.meta r.projected
  apply («prefix».add projection).of_le
  intro h i
  let s := p h i
  change s.endAddress 0 ≤ s.count + DescentResetStemProject.endAddress 0 s.fields
    (s.oldHosts*s.shapes) s.groups s.blocks s.metaBits s.oldBatch s.batch
  apply le_of_eq
  rw [endAddress,DescentResetStemProject.extent (s.projected 0), projected, Nat.zero_add]

end Hierarchy.DescentPrivateMaskDeck.Shape

end OAI
