import OAI.Hierarchy.DescentOrdinaryPalettePaidRows
import OAI.Hierarchy.DescentDatedPrimitivePitch

namespace OAI
/-! Actual canonical ordinary working and returned lanes discharge the internal ROM widths and row fill. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryPrimitiveCheckpoint DescentOrdinaryPalette DescentSIMDLookup
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
variable (p h unit prior : ℕ)
local notation "L" => v.paletteShape
local notation "b" => (L).primitiveBits
local notation "a" => Configuration.workUnit v.reference.degree v.reference.k v.reference.capacity v.reference.oldNodes v.resolver.nodes b
local notation "d" => Configuration.returnUnit b v.resolver.nodes

theorem primitive_funding
    (configured : v.palette=Configuration.atOrdinary v.gadget v.schedule v.palette.rotor p h
      v.reference.degree v.reference.k v.reference.capacity v.reference.oldNodes v.resolver.nodes prior)
    (old : Layout.Filled h unit (L).priorLanes) (birth : Layout.Filled h unit (L).birthLanes)
    (origin : Layout.Filled h unit (L).originLanes)
    (oldFit : (b*v.reference.oldNodes)*(L).priorLanes≤h/2) (newFit : b*(L).birthLanes≤h/2)
    (idFit : ((L).originBits*v.resolver.nodes)*(L).originLanes≤h/2)
    (room : 2*a≤h) (cost : 4*a≤unit) (nextRoom : 2*d≤h) (nextCost : 4*d≤unit) :
    (L).Funding h unit:=by
  have workEq : (L).workLanes=lanes h a:=by
    have cw:=congrArg Configuration.workLanes configured
    have cs:=congrArg Configuration.seedWidth configured
    have cz:=congrArg Configuration.grainLimit configured
    change v.palette.workLanes=_
    simpa only [Configuration.atOrdinary,paletteShape,cs,cz] using cw
  have nextEq : (L).nextLanes=Configuration.returned h b v.resolver.nodes:=by
    obtain cs:=congrArg Configuration.seedWidth configured
    obtain cz:=congrArg Configuration.grainLimit configured
    simpa only [paletteShape,Configuration.atOrdinary,cs,cz] using congrArg Configuration.nextLanes configured
  have unitPos : 0<a:=(Nat.zero_lt_one.trans_le (Nat.le_max_left ..))
  have why:=occupancy h a unitPos room
  have fill : h≤(L).workLanes*unit:=by
    rw [workEq]
    exact why.2.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using
      (Nat.mul_le_mul_left (lanes h a) cost))
  have live : Layout.Filled h unit (L).workLanes:=
    ⟨by rw [workEq];exact why.1,by rw [workEq];exact Nat.div_le_self ..,fill⟩
  have last:=Configuration.returned_occupancy h b v.resolver.nodes nextRoom
  have refill : h≤(L).nextLanes*unit:=by
    rw [nextEq]
    exact last.2.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using
      (Nat.mul_le_mul_left (Configuration.returned h b v.resolver.nodes) nextCost))
  have returned : Layout.Filled h unit (L).nextLanes:=⟨by rw [nextEq];exact last.1,by rw [nextEq];exact Nat.div_le_self ..,refill⟩
  have block : 0<(L).blocks:=Nat.two_pow_pos _
  have large : Layout.Filled h unit (L).oldWork:=by
    refine ⟨Nat.mul_pos live.positive block,?_,fill.trans (Nat.mul_le_mul_right unit (Nat.le_mul_of_pos_right _ block))⟩
    change (L).workLanes*(L).blocks≤h
    rw [workEq]
    have rb : (L).blocks≤a:=(Nat.le_max_left ..).trans (Nat.le_max_right ..)
    exact (Nat.mul_le_mul_left _ rb).trans ((lanes_fit h a).trans (Nat.div_le_self ..))
  have keys:=Configuration.work_room h v.reference.degree v.reference.k v.reference.capacity v.reference.oldNodes v.resolver.nodes b
  refine ⟨old,birth,origin,live,large,returned,oldFit,newFit,idFit,?_,?_,?_,?_,?_⟩
  · change b*v.resolver.nodes*(L).workLanes≤h/2
    rw [workEq];exact keys.2.2.2.2
  · change b*v.reference.oldNodes*((L).workLanes*(L).blocks)≤h/2
    rw [workEq];exact keys.1
  · change _*((L).workLanes*(L).blocks)≤h/2
    rw [workEq];exact keys.2.1
  · change (b*(L).candidates)*(L).blocks*(L).workLanes≤h/2
    rw [workEq];exact keys.2.2.1
  · change ((L).originBits*(L).newNodes+b*(L).candidates)*(L).workLanes≤h/2
    rw [workEq];exact keys.2.2.2.1

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
