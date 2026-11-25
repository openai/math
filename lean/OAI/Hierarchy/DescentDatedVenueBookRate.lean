import OAI.Hierarchy.DescentStageVenueBookLayout
import OAI.Hierarchy.DescentVenueShapeRate

namespace OAI
/-! # Uniform public address width of the successor input books -/
namespace Hierarchy.DescentSixParty.StageVenueTail.Date
open DescentDatedAddressBook DescentSIMDLookup Filter
noncomputable section
variable {ι:ℕ→Type*} (P:∀h,ι h→Date)

structure ScalarRoom : Prop where
  blocks : Bounded (fun h i=>2^(P h i).k)
  hosts : Bounded (fun h i=>(P h i).hosts)
  groups : Bounded (fun h i=>(P h i).groups)
  degree : Bounded (fun h i=>(P h i).degree)
  cap : Bounded (fun h i=>(P h i).cap)
  issuedLanes : Bounded (fun h i=>(P h i).lanes)
  signedLanes : Bounded (fun h i=>(P h i).signedLanes)
  aliveLanes : Bounded (fun h i=>(P h i).aliveLanes)
  paidLanes : Bounded (fun h i=>(P h i).paidLanes)
  signedWidth : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,
    DescentSignedCableCodec.width (P h i).degree (P h i).cap*(P h i).signedLanes≤C*h
  fundedWidth : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(P h i).paidBits*(P h i).paidLanes≤C*h
  actorWidth : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(P h i).aliveLanes≤C*h
  maskWidth : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(P h i).lanes≤C*h

theorem extent_rate (r:ScalarRoom P):Bounded (fun h i=>(P h i).endAddress 0):=by
  have signed:=DescentVenueSlabs.extent_rate (fun h i=>(P h i).signedShape)
    (r.blocks.mul ((Bounded.const 2).mul r.cap)) r.hosts r.groups r.signedLanes r.issuedLanes r.signedWidth
  have paid:=DescentVenueSlabs.extent_rate (fun h i=>(P h i).paidShape)
    r.blocks r.hosts r.groups r.paidLanes r.issuedLanes r.fundedWidth
  have actors:=DescentVenueSlabs.extent_rate (fun h i=>(P h i).aliveShape)
    r.blocks r.hosts r.groups r.aliveLanes r.issuedLanes (by simpa only [aliveShape,Nat.one_mul] using r.actorWidth)
  have chunks_:Bounded (fun h i=>chunks (P h i).groups (P h i).lanes):=
    (r.groups.add r.issuedLanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows:=r.hosts.mul chunks_
  have entries:=r.hosts.mul r.degree
  have dirs:=(r.degree.mul rows).add (r.hosts.add (rows.add entries))
  have slack:=(((entries.max' (rows.max' r.hosts)).add (Bounded.const 1)).padded)
  obtain ⟨C,bound⟩:=r.maskWidth
  have lookup:=r.blocks.mul (Bounded.pow_of_linear (K:=C) bound)
  have booking:=(((lookup.add rows.padded).add dirs).add slack)
  apply ((((signed.add paid).add actors).add booking)).of_le
  intro h i
  let d:=P h i
  change d.endAddress 0≤_
  rw [endAddress,thirdEnd,DescentVenueSlabs.translates,secondEnd,
    DescentVenueSlabs.translates,firstEnd]
  simp only [StageVenueTail.endAddress,StageVenueTail.area,DescentActorRaster.Venue.outBase,DescentPackedColumnSum.finish,
    StageVenueTail.span,DescentScalarHaloPortROM.stop,DescentScalarHaloPortROM.length,DescentScalarHaloPortROM.pad,
    Nat.one_mul,Nat.add_assoc]; rfl

end
end Hierarchy.DescentSixParty.StageVenueTail.Date

end OAI
