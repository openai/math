import OAI.Hierarchy.DescentDatedOrdinaryPrimitiveRate

namespace OAI
/-! A single address exponent for every physical primitive shape within the given numerical bounds. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook Filter
noncomputable section
variable {F : Type} [Field F]

structure PrimitiveAperture (C h : ℕ) {P : Type} (v : PhysicalOrdinary F P) : Prop where
  hosts : v.paletteShape.hosts≤2^(C*h)
  groups : v.paletteShape.groups≤2^(C*h)
  lows : v.paletteShape.lows≤2^(C*h)
  blocks : v.paletteShape.blocks≤2^(C*h)
  ports : v.paletteShape.ports≤2^(C*h)
  cap : v.paletteShape.capacity≤2^(C*h)
  old : v.paletteShape.oldNodes≤2^(C*h)
  prior : v.paletteShape.priorLanes≤2^(C*h)
  birth : v.paletteShape.birthLanes≤2^(C*h)
  origin : v.paletteShape.originLanes≤2^(C*h)
  work : v.paletteShape.workLanes≤2^(C*h)
  next : v.paletteShape.nextLanes≤2^(C*h)
  donorHosts : v.bornBook.hosts≤2^(C*h)
  donorGroups : v.bornBook.groups≤2^(C*h)
  donorBlocks : v.bornBook.blocks≤2^(C*h)
  donorCap : v.bornBook.cap≤2^(C*h)
  packed : primitivePeak v≤C*h

/-- The aperture indexes the actual layouts across all alphabets and all calendars. -/
theorem uniform_primitive_aperture (C : ℕ) :
    ∃K : ℕ,∀ᶠ h : ℕ in atTop,∀{P : Type} (v : PhysicalOrdinary F P),
      PrimitiveAperture C h v → v.primitiveRoof 0≤2^(K*h):=by
  let ι (h : ℕ) := Σ P : Type,{v : PhysicalOrdinary F P // PrimitiveAperture C h v}
  let family (h : ℕ) (i : ι h) : PhysicalOrdinary F i.1:=i.2.val
  have scalar (f : ∀h,ι h→ℕ) (bound : ∀h i,f h i≤2^(C*h)) : Bounded f :=
    ⟨C,Eventually.of_forall bound⟩
  have room : PrimitiveScalarRoom family :=
    {
      hosts :=scalar _ (fun h i=>i.2.property.hosts)
      groups :=scalar _ (fun h i=>i.2.property.groups)
      lows :=scalar _ (fun h i=>i.2.property.lows)
      blocks :=scalar _ (fun h i=>i.2.property.blocks)
      ports :=scalar _ (fun h i=>i.2.property.ports)
      cap :=scalar _ (fun h i=>i.2.property.cap)
      old :=scalar _ (fun h i=>i.2.property.old)
      prior :=scalar _ (fun h i=>i.2.property.prior)
      birth :=scalar _ (fun h i=>i.2.property.birth)
      origin :=scalar _ (fun h i=>i.2.property.origin)
      work :=scalar _ (fun h i=>i.2.property.work)
      next :=scalar _ (fun h i=>i.2.property.next)
      donorHosts :=scalar _ (fun h i=>i.2.property.donorHosts)
      donorGroups :=scalar _ (fun h i=>i.2.property.donorGroups)
      donorBlocks :=scalar _ (fun h i=>i.2.property.donorBlocks)
      donorCap :=scalar _ (fun h i=>i.2.property.donorCap)
      packed :=⟨C,Eventually.of_forall fun h i=>i.2.property.packed⟩ }
  obtain ⟨K,large⟩:=primitive_rate family room
  refine ⟨K,large.mono ?_⟩
  intro h all P v measured
  exact all ⟨P,v,measured⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
