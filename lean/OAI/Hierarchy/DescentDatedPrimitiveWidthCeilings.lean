import OAI.Hierarchy.DescentFundedPrimitivePeak

namespace OAI
/-! Absolute word-key widths for the five stored primitive passes, including empty batches. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryPrimitiveCheckpoint DescentOrdinaryPalette DescentSIMDLookup
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (p h prior : ℕ)
local notation "L" => v.paletteShape
local notation "b" => (L).primitiveBits
local notation "a" => Configuration.workUnit v.reference.degree v.reference.k v.reference.capacity v.reference.oldNodes v.resolver.nodes b

theorem primitive_width_ceilings
    (configured : v.palette=Configuration.atOrdinary v.gadget v.schedule v.palette.rotor p h
      v.reference.degree v.reference.k v.reference.capacity v.reference.oldNodes v.resolver.nodes prior)
    (chip : (2*v.bornBook.chipBits)*v.bornBook.lanes≤h/2)
    (oldFit : (b*v.reference.oldNodes)*(L).priorLanes≤h/2) (newFit : b*(L).birthLanes≤h/2)
    (idFit : ((L).originBits*v.resolver.nodes)*(L).originLanes≤h/2) :
    primitivePeak v≤h/2 ∧ (L).workLanes≤h ∧ (L).nextLanes≤h:=by
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
  have keys:=Configuration.work_room h v.reference.degree v.reference.k v.reference.capacity
    v.reference.oldNodes v.resolver.nodes b
  refine ⟨?_,by rw [workEq];exact Nat.div_le_self ..,by rw [nextEq];exact Nat.div_le_self ..⟩
  simp only [primitivePeak,List.foldr,max_le_iff]
  refine ⟨?_,oldFit,newFit,idFit,?_,?_,?_,?_,?_,Nat.zero_le _⟩
  · simpa only [DescentOperandFamilyBook.unit,Nat.mul_one,two_mul] using chip
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
