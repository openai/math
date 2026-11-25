import OAI.Hierarchy.DescentFundedClipNumbers

namespace OAI
/-! # All address widths of the clipped paid and activity rasters -/
namespace Hierarchy.DescentSixParty.StageVenueTail.OrdinaryRaster
open Chronology.PhysicalOrdinary DescentPacking.PackedMatch.Local.Stage.Dated DescentPackedActorMask
open DescentOrdinaryVenueIngress DescentPaidResidentCount DescentVenueQuantityPlanes DescentDatedAddressBook Filter
noncomputable section
set_option quotPrecheck false
variable {ι : ℕ→Type*} (a : ∀h,ι h→Ordinary) (d : ∀h,ι h→Date)
variable (socket : ∀h,ι h→DescentRawCablePanel.DepotRAM.Shape) (donor extra : ∀h,ι h→ℕ)
local notation "clip" h:arg i:arg => fundedClipAt (a h i) (socket h i) (donor h i) (d h i).paidBits (extra h i)
local notation "dims_" h:arg i:arg => dims (a h i) (d h i) ((clip h i).working)

theorem funded_room (payload : ∀h i,(a h i).payload=h) (post : ∀h i,(d h i).paidLanes=(clip h i).postPitch)
    (fees : ∀ᶠ h : ℕ in atTop,∀i,(d h i).paidBits≤(a h i).unit)
    (degree : Bounded (fun h i=>(a h i).D)) (radix : Bounded (fun h i=>2^(a h i).k))
    (oldHosts : Bounded (fun h i=>(a h i).H)) (newHosts : Bounded (fun h i=>(d h i).hosts))
    (oldGroups : Bounded (fun h i=>(a h i).G)) (newGroups : Bounded (fun h i=>(d h i).groups)) :
    ScalarRoom a d (fun h i=>(clip h i).working) :=by
  have slots : Bounded (fun h i=>DescentOrdinaryVenueReturn.shapeSlots (a h i).D) :=by
    have padded:=((Bounded.const 2).mul degree).padded
    have scale:=((Bounded.const (2^20)).mul (padded.pow 34)).add (Bounded.const 2)
    simpa only [DescentOrdinaryVenueReturn.shapeSlots,DescentHostDegree.packExponent,
      DescentHostDegree.logDegree,Nat.pow_add,Nat.mul_comm 34 _,Nat.pow_mul] using scale
  have sheets : Bounded (fun h i=>shapes (a h i)) :=by
    have upper:=(radix.mul (Bounded.const 2)).mul slots
    apply upper.of_le
    intro h i
    unfold shapes
    rw [Nat.pow_succ]
    apply Nat.mul_le_mul_right
    exact Nat.sub_le ..
  have oldCap (h) (i : ι h) : (a h i).lanesAt≤h :=(Nat.div_le_self ..).trans_eq (payload h i)
  have clipCap (h) (i : ι h) : (clip h i).working≤h := (clip h i).working_fields.2.1.trans (oldCap h i)
  have postCap (h) (i : ι h) : (d h i).paidLanes≤h :=by
    rw [post]
    exact (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans (clipCap h i)
  have height : Bounded (fun h (_ : ι h)=>h) :=⟨1,Eventually.of_forall fun h _=>by
    simpa only [Nat.one_mul] using (Nat.lt_two_pow_self (n:=h)).le⟩
  have key (h) (i : ι h) :
      Sweep.maskBits (donors (a h i)) (a h i).cap (nameBits (a h i)) (clip h i).working≤h ∧
      Sweep.sumBits (donors (a h i)) (a h i).cap (d h i).paidBits (clip h i).working≤h ∧
      (d h i).paidBits*(clip h i).working≤h :=by
    let c:=clip h i
    let b:=(d h i).paidBits
    let D:=donors (a h i)
    let n:=nameBits (a h i)
    let A:=DescentPackedActorMask.actors D (a h i).cap
    have paidUnit : fundedUnitAt (a h i) b≤c.unit :=(le_max_left ..).trans (le_max_right ..)
    have cover : max (b*D+b) (max (n*A) (1*A+b*D))≤c.unit:=paidUnit
    have fit {u : ℕ} (used : u≤c.unit) : u*c.working≤h :=by
      calc u*c.working ≤ c.unit*c.working := Nat.mul_le_mul_right _ used
           _ = c.working*c.unit := Nat.mul_comm ..
           _ ≤ (a h i).payload/4 := c.working_fields.2.2
           _ ≤ h := (Nat.div_le_self ..).trans_eq (payload h i)
    exact ⟨fit ((le_max_left ..).trans ((le_max_right ..).trans cover)),
      fit ((le_max_right ..).trans ((le_max_right ..).trans cover)),
      fit ((Nat.le_add_left ..).trans ((le_max_left ..).trans cover))⟩
  have paid (h) (i : ι h) : ((d h i).paidBits*2^(a h i).k)*(d h i).paidLanes≤h :=by
    rw [post]
    calc _ = (d h i).paidBits*((clip h i).postPitch*2^(a h i).k) :=by ring
         _ ≤ h :=(key h i).2.2
  have alive (h) (i : ι h) : (1*2^(a h i).k)*(d h i).paidLanes≤h :=by
    rw [post,Nat.one_mul,Nat.mul_comm]
    exact clipCap h i
  have bounds {x : ∀h,ι h→ℕ} (fit : ∀h i,x h i≤h) :
      ∃C : ℕ,∀ᶠ h : ℕ in atTop,∀i,x h i≤C*h :=
    ⟨1,Eventually.of_forall fun h i=>by simpa only [Nat.one_mul] using fit h i⟩
  have paidRoom : State.ScalarRoom (fun h i=>dims_ h i) :=
    ⟨sheets,oldHosts,newHosts,newGroups,radix,height.of_le clipCap,height.of_le postCap,
      bounds (fun h i=>(key h i).2.2),bounds paid⟩
  have bitRoom : State.ScalarRoom (fun h i=>DescentOrdinaryRasterReturn.actor (dims_ h i)) :=
    ⟨sheets,oldHosts,newHosts,newGroups,radix,height.of_le clipCap,height.of_le postCap,
      bounds (fun h i=>by
        change 1*(clip h i).working ≤ h
        simpa only [Nat.one_mul] using clipCap h i),bounds alive⟩
  refine ⟨height.of_le oldCap,⟨1,?_⟩,⟨paidRoom,bitRoom⟩,(degree.add (Bounded.const 1)).pow 4,
    oldGroups,bounds (fun h i=>(key h i).1),bounds (fun h i=>(key h i).2.1)⟩
  filter_upwards [fees] with h fee
  intro i
  have sum:=Nat.mul_le_mul_right (a h i).lanesAt (fee i)
  have fits:=DescentSIMDLookup.lanes_fit (a h i).payload (a h i).unit
  rw [Nat.mul_comm] at fits
  exact sum.trans (fits.trans ((Nat.div_le_self ..).trans (by simp [payload])))

end
end Hierarchy.DescentSixParty.StageVenueTail.OrdinaryRaster

end OAI
