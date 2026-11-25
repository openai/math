import OAI.Hierarchy.DescentFundedRasterRoomNumbers

namespace OAI
/-! # A single public exponent for every funded ordinary raster under common scalar caps -/
namespace Hierarchy.DescentSixParty.StageVenueTail.OrdinaryRaster
open Chronology.PhysicalOrdinary DescentPacking.PackedMatch.Local.Stage.Dated DescentDatedAddressBook Filter
set_option quotPrecheck false
noncomputable section

structure ScalarCaps (a : Ordinary) (d : Date) (h K : ℕ) : Prop where
  degree : a.D≤2^(K*h)
  radix : 2^a.k≤2^(K*h)
  oldHosts : a.H≤2^(K*h)
  newHosts : d.hosts≤2^(K*h)
  oldGroups : a.G≤2^(K*h)
  newGroups : d.groups≤2^(K*h)

private structure Row (K h : ℕ) where
  area : Ordinary
  date : Date
  shape : DescentRawCablePanel.DepotRAM.Shape
  donor : ℕ
  extra : ℕ
  payload : area.payload=h
  post : date.paidLanes=(fundedClipAt area shape donor date.paidBits extra).postPitch
  fees : date.paidBits≤area.unit
  bounds : ScalarCaps area date h K

/-- The exponent is chosen before both calendar parameters. This estimate also
applies to a family of schedules with different clipping units and packing widths. -/
theorem uniform_space (K : ℕ) : ∃C : ℕ,∀ᶠ h : ℕ in atTop,∀ (a : Ordinary) (d : Date)
    (shape : DescentRawCablePanel.DepotRAM.Shape) (donor extra : ℕ),
    let clip:=fundedClipAt a shape donor d.paidBits extra
    a.payload=h→d.paidLanes=clip.postPitch→d.paidBits≤a.unit→ScalarCaps a d h K→
      roof a d clip.working 0≤(2^h)^C :=by
  let A (h) (r : Row K h):=r.area
  let V (h) (r : Row K h):=r.date
  let socket (h) (r : Row K h):=r.shape
  let panel (h) (r : Row K h):=r.donor
  let more (h) (r : Row K h):=r.extra
  have bounded (x : ∀h,Row K h→ℕ) (b : ∀h r,x h r≤2^(K*h)) : Bounded x:=
    ⟨K,Eventually.of_forall b⟩
  have space:=funded_room A V socket panel more (fun _ r=>r.payload) (fun _ r=>r.post)
    (Eventually.of_forall (fun _ r=>r.fees)) (bounded _ (fun _ r=>r.bounds.degree))
    (bounded _ (fun _ r=>r.bounds.radix)) (bounded _ (fun _ r=>r.bounds.oldHosts))
    (bounded _ (fun _ r=>r.bounds.newHosts)) (bounded _ (fun _ r=>r.bounds.oldGroups))
    (bounded _ (fun _ r=>r.bounds.newGroups))
  obtain ⟨C,ready⟩:=extent_rate _ _ _ space
  refine ⟨C,?_⟩
  filter_upwards [ready] with h good
  intro a d shape donor extra clip payload post fees bounds
  let r : Row K h:=⟨a,d,shape,donor,extra,payload,post,fees,bounds⟩
  exact (good r).trans_eq (by rw [←pow_mul,Nat.mul_comm])

end
end Hierarchy.DescentSixParty.StageVenueTail.OrdinaryRaster

end OAI
