import OAI.Hierarchy.DescentResetCanvasIngressShape
import OAI.Hierarchy.DescentVenueShapeRate

namespace OAI
/-! # Physical word extent of the two input retilings and the reset amount collector -/
namespace Hierarchy.DescentResetCanvasIngress.Layout
open DescentDatedAddressBook DescentSIMDLookup ProtocolRAM Filter
noncomputable section

private theorem signed_translate (s : Layout) (base : ℕ) :
    s.signedEnd base = base+s.signedEnd 0 := by
  simp only [signedEnd,DescentResetSignedTokens.Layout.endAddress,DescentResetSignedTokens.Layout.start,
    DescentResetSignedTokens.Layout.dictionary,Bank.size]
  rw [DescentVenueSlabs.translates s.signed.venue base]
  simp only [Nat.add_assoc]

theorem translate (s : Layout) (base : ℕ) :
    s.endAddress base = base+s.endAddress 0 := by
  simp only [endAddress,DescentResetCanvasAmount.Layout.endAddress,DescentResetCanvasAmount.Layout.amount,
    DescentResetCanvasAmount.Layout.table,atomEnd]
  rw [DescentVenueSlabs.translates s.amounts (s.signedEnd base), signed_translate s base,
    DescentVenueSlabs.translates s.amounts (s.signedEnd 0)]
  simp only [Nat.add_assoc]

theorem after (s : Layout) (base : ℕ) : base ≤ s.endAddress base := by
  rw [translate]
  exact Nat.le_add_right ..

variable {ι : ℕ→Type*} (p : ∀h,ι h→Layout)

structure ScalarRoom : Prop where
  blocks : Bounded (fun h i=>2^(p h i).k)
  hosts : Bounded (fun h i=>(p h i).hosts)
  groups : Bounded (fun h i=>(p h i).groups)
  cap : Bounded (fun h i=>(p h i).cap)
  oldLanes : Bounded (fun h i=>(p h i).sourceLanes)
  lanes : Bounded (fun h i=>(p h i).targetLanes)
  oldSigned : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(p h i).signed.bits*(p h i).sourceLanes ≤ C*h
  oldAmount : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(p h i).oldBits*(p h i).sourceLanes ≤ C*h
  collector : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,max (p h i).oldBits (p h i).signed.bits*(p h i).targetLanes ≤ C*h

theorem rate (r : ScalarRoom p) : Bounded (fun h i=>(p h i).endAddress 0) := by
  let two := Bounded.const (ι:=ι) 2
  have slots := r.blocks.mul (two.mul r.cap)
  have signedVenue := DescentVenueSlabs.extent_rate (fun h i=>(p h i).signed.venue)
    slots r.hosts r.groups r.oldLanes r.lanes r.oldSigned
  have amountVenue := DescentVenueSlabs.extent_rate (fun h i=>(p h i).amounts)
    r.blocks r.hosts r.groups r.oldLanes r.lanes r.oldAmount
  have chunk : Bounded (fun h i=>chunks (p h i).groups (p h i).targetLanes) :=
    (r.groups.add r.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows := r.hosts.mul chunk
  obtain ⟨C,cap⟩:=r.collector
  have lookup : Bounded (fun h i=>2^((p h i).collector.unitBits*(p h i).targetLanes)) :=
    Bounded.pow_of_linear (K:=C) cap
  have signedLookup : Bounded (fun h i=>2^((p h i).signed.bits*(p h i).targetLanes)) := by
    apply lookup.of_le
    intro h i
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_right ..))
  have signedTop : Bounded (fun h i=>(p h i).signedEnd 0) :=
    ((signedVenue.add signedLookup).add (slots.mul rows)).add rows.padded
  have atomTop : Bounded (fun h i=>(p h i).atomEnd 0) := by
    apply (signedTop.add amountVenue).of_le
    intro h i
    exact (DescentVenueSlabs.translates (p h i).amounts ((p h i).signedEnd 0)).le
  have count := r.blocks.add (slots.mul two)
  exact ((atomTop.add rows.padded).add (count.mul lookup)).add rows.padded

end
end Hierarchy.DescentResetCanvasIngress.Layout

end OAI
