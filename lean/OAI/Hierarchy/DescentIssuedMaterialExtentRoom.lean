import OAI.Hierarchy.DescentMaterialIssuedDigit
import OAI.Hierarchy.DescentNamedSignedReturn

namespace OAI
/-! The three ROM and operand apertures at the true old and new packing pitches. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentRawCablePanel DescentDatedAddressBook DescentSIMDLookup Filter
set_option quotPrecheck false
variable {F Pin:Type} [Field F] (v:PhysicalOrdinary F Pin)
include v in
theorem material_widths (chosen:v.signedLayout.format v.payload=v.signed)
    (enough:256≤v.prior.placement.cap) :
    v.material.keyBits≤v.payload/2 ∧ v.material.fieldBits*v.material.oldLanes≤v.payload/2 ∧
    v.material.socketBits≤v.payload/2 :=by
  let fmt:=v.ticket.depotShape v.short
  let size:=v.ticket.installedDonorWidth v.short v.profile
  have old:2*DepotRAM.totalBits fmt+1≤ size:=(v.ticket.installed_donor_widths v.short v.profile).2.2
  have chart:DepotRAM.chartBits fmt≤DepotRAM.totalBits fmt:=by unfold DepotRAM.totalBits;omega
  have both:DepotRAM.totalBits fmt+DepotRAM.chartBits fmt≤ size:=by omega
  have paid:=lanes_fit v.payload size
  have chip (m:ℕ) (hm:m≤ size) : m*lanes v.payload size≤v.payload/2:=
    (Nat.mul_le_mul_right _ hm).trans (by simpa only [Nat.mul_comm] using paid)
  have field : v.signed.fieldBits ≤ size := by
    rw [←chosen]
    change v.signedLayout.fieldBits ≤ size
    exact (Nat.le_succ _).trans (v.signed_digit_fits enough)
  refine ⟨chip _ both,chip _ field,?_⟩
  change (v.signed.fieldBits*2^v.k+v.signed.fieldBits)*v.signed.lanes≤_
  rw [←chosen];exact v.signedLayout.material_width v.payload

variable {ι:ℕ→Type*} {Pins:∀h,ι h→Type} (V:∀h (i:ι h),PhysicalOrdinary F (Pins h i))
local notation "a" h:arg i:arg=>(V h i).area
local notation "s" h:arg i:arg=>(V h i).signed
local notation "e" h:arg i:arg=>(V h i).material

theorem material_extent_room
    (payload:∀h i,(V h i).payload=h) (chosen:∀h i,(V h i).signedLayout.format h=s h i)
    (enough:∀h i,256≤(V h i).prior.placement.cap)
    (houses:Bounded (fun h i=>(a h i).H)) (groups:Bounded (fun h i=>(a h i).G))
    (nextH:Bounded (fun h i=>(s h i).hosts)) (nextG:Bounded (fun h i=>(s h i).groups))
    (blocks:Bounded (fun h i=>2^(V h i).k)) (degree:Bounded (fun h i=>(V h i).prior.placement.degree))
    (capacity:Bounded (fun h i=>(V h i).prior.placement.cap)) :
    MaterialExtent.ScalarRoom (fun h i=>e h i) :=by
  have hroom:Bounded (ι:=ι) (fun h _=>h):=
    ⟨1,Filter.Eventually.of_forall fun h _=>by simpa only [Nat.one_mul] using (Nat.lt_two_pow_self (n:=h)).le⟩
  have signed (h:ℕ) (i:ι h) : (V h i).signedLayout.format (V h i).payload=s h i:=by rw [payload,chosen]
  have widths (h:ℕ) (i:ι h):= (V h i).material_widths (signed h i) (enough h i)
  have path:= (degree.add (Bounded.const 1)).pow 4
  refine ⟨houses,groups,hroom.of_le ?_,nextH,nextG,hroom.of_le ?_,blocks,path.of_le ?_,capacity,?_,?_,?_⟩
  · intro h i
    change lanes (V h i).payload _≤h
    rw [payload];exact Nat.div_le_self ..
  · intro h i
    change (s h i).lanes≤h
    rw [←chosen];exact Nat.div_le_self ..
  · intro h i
    change (s h i).reach≤_
    rw [←chosen]
    exact le_rfl
  · refine ⟨1,Filter.Eventually.of_forall ?_⟩
    intro h i
    exact ((widths h i).1.trans (Nat.div_le_self _ 2)).trans_eq ((payload h i).trans (Nat.one_mul h).symm)
  · refine ⟨1,Filter.Eventually.of_forall ?_⟩
    intro h i
    exact ((widths h i).2.1.trans (Nat.div_le_self _ 2)).trans_eq ((payload h i).trans (Nat.one_mul h).symm)
  · refine ⟨1,Filter.Eventually.of_forall ?_⟩
    intro h i
    exact ((widths h i).2.2.trans (Nat.div_le_self _ 2)).trans_eq ((payload h i).trans (Nat.one_mul h).symm)

end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
