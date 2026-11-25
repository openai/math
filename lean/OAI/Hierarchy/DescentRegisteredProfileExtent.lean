import OAI.Hierarchy.DescentRegisteredOrdinaryGeometry
import OAI.Hierarchy.DescentNamedRegisteredStaticCore

namespace OAI
/-! # Size of the actual ordinary donor's epoch shelf conversion -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentCompiler DescentPacking.PackedMatch DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {ι : ℕ→Type*}
    (a : ∀h,ι h→Dated.Ordinary) (seats : ∀h,ι h→ℕ)
local notation "width_" => DescentTerminalEpochBits.width G.C
local notation "profile_" h:arg i:arg =>(⟨seats h i,DescentPackedEpochShelves.grain (h/2) G.C,
  (a h i).lanesAt*(a h i).shapeAt.pairs,width_⟩:ProfileRepack)

/-- The same measured six-birth aperture pays the entire new pitch, including
the additional marker bit. This estimate allows physically empty shelves. -/
theorem profile_extent_room (booked : Bounded seats) (payload : ∀h i,(a h i).payload=h)
    (letters : ∀h i,(a h i).profile=width_)
    (six : ∀h i,SixBirths.unit (a h i).shapeAt≤(a h i).unit) :
    ProfileRepack.ScalarRoom (fun h i=>profile_ h i) :=by
  have ambient : Bounded (fun h (_:ι h)=>h):=
    ⟨1,Eventually.of_forall fun h i=>by simpa only [one_mul] using (Nat.lt_two_pow_self (n:=h)).le⟩
  have earlier (h : ℕ) : DescentPackedEpochShelves.grain (h/2) G.C≤h:=
    (Nat.div_le_self ..).trans (Nat.div_le_self ..)
  have old (h : ℕ) : width_*DescentPackedEpochShelves.grain (h/2) G.C≤h:=by
    have paid:=lanes_fit (h/2) (DescentPackedEpochShelves.unit G.C)
    change DescentPackedEpochShelves.grain (h/2) G.C*(width_+1)≤_ at paid
    rw [Nat.mul_add,Nat.mul_comm _ width_,Nat.mul_one] at paid
    omega
  have new_ (h : ℕ) (i:ι h) : (width_+1)*((a h i).lanesAt*(a h i).shapeAt.pairs)≤h:=by
    let d:=a h i
    have low : width_≤d.shapeAt.digit:=by
      rw [←letters h i]
      exact (shape_width ..).2.2.2
    have u : (d.shapeAt.digit+1)*(d.shapeAt.pairs*6)≤d.unit :=
      (Nat.le_max_right ..).trans (six h i)
    have u' : (width_+1)*d.shapeAt.pairs≤d.unit:=
      (Nat.mul_le_mul (Nat.add_le_add_right low 1) (Nat.le_mul_of_pos_right _ (by decide : 0<6))).trans u
    have chosen:=lanes_fit d.payload d.unit
    change d.lanesAt*d.unit≤d.payload/2 at chosen
    calc
      _ = d.lanesAt*((width_+1)*d.shapeAt.pairs):=by ring
      _ ≤ d.lanesAt*d.unit:=Nat.mul_le_mul_left _ u'
      _ ≤ h:=(chosen.trans (Nat.div_le_self ..)).trans (payload h i).le
  refine ⟨booked,ambient.of_le (fun h _=>earlier h),ambient.of_le (fun h i=>?_),⟨1,?_⟩,⟨1,?_⟩⟩
  · exact (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ _)).trans (new_ h i)
  · exact Eventually.of_forall fun h i=>by simpa only [Nat.one_mul] using old h
  · apply Eventually.of_forall
    intro h i
    have hi:=new_ h i
    rw [Nat.add_mul,Nat.one_mul] at hi
    simpa only [Nat.one_mul] using (Nat.le_add_right ..).trans hi

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
