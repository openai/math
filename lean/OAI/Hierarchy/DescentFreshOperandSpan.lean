import OAI.Hierarchy.DescentOrdinaryBornInventory
import OAI.Hierarchy.DescentFreshRoleHeaderData
import OAI.Hierarchy.DescentRangePage

namespace OAI
/-! The three range fields of a fresh party operand, including unused slots. -/
namespace Hierarchy.DescentOrdinaryBorn
open DescentSixParty DescentKernelHistory DescentOperandPhysicalInput DescentRawCablePanel
open DescentOperandStateBanks DescentBundleHistory DescentSIMDLookup
open scoped Classical BigOperators Fin.CommRing
noncomputable section

set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F)
variable {l n u : ℕ}
local notation "code" => DescentPacking.PackedMatch.LayoutSum.profileCode G.C

theorem inventory_arity (p z : ℕ) (a : Profile G.C) (party : Fin 6) :
    (inventory (actual G p) z (code a).val party).length =
      DescentFreshRoleFields.arity G p z a party := by
  have unitsAt (r : RolePort party) :
      units (actual G p) z (code a).val (role r) = DescentFreshRoleFields.width G z a party r / p := by
    rcases r with (s|s)|(s|s) <;> simp only [units,actual,role,DescentFreshRoleFields.width,profile_read]
  simp only [inventory,group,List.length_flatMap,List.finRange,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,List.length_map,List.length_range,DescentFreshRoleFields.arity,
    DescentFreshRoleFields.widths,unitsAt]

/-- Every live fresh operand is a single word with zero start and unit stride.
The same physical field reader zero-fills the entire remaining rectangle. -/
theorem selected_span (p z arg bits : ℕ) (wide : 0 < bits) (a : Profile G.C)
    (party : Fin 6) (f : Fin 3) (d : Donor l n u)
    (first : d.first=true) (counts : ∀e,(d.supplyUnits e).val=(a.val e).val+G.k) :
    (component bits (pointerAt G.b p z d party arg) (DescentRetainedRangeDigits.page f)).val =
      if arg < DescentFreshRoleFields.arity G p z a party then (if f.val=0 then 0 else 1) else 0 := by
  have supplied (e : Fin 8) :
      (d.supplyUnits e).val=(profileDigits (actual G p).capacity (code a).val e).val+(actual G p).supplyOffset := by
    simpa only [actual,profile_read] using counts e
  have eqn:=component_first (actual G p) z (code a).val arg bits party d first supplied
    (DescentRetainedRangeDigits.page f)
  change (component bits (pointerAt (actual G p).demand (actual G p).grain z d party arg) _).val=_
  rw [eqn]
  let deck:=inventory (actual G p) z (code a).val party
  have size : deck.length=DescentFreshRoleFields.arity G p z a party:=inventory_arity G p z a party
  by_cases live : arg < deck.length
  · rw [ite_eq_left (size ▸ live)]
    have hit : mouth (actual G p) z (code a).val party arg=some deck[arg] := List.getElem?_eq_getElem live
    have small : 1 < 2^bits:=Nat.one_lt_pow (Nat.ne_of_gt wide) (by decide)
    have span (m : Mouth) : (Pointer.cable 0 0 m.chunk).fields ⟨0,1,1⟩ (DescentRetainedRangeDigits.page f)=
        (if f.val=0 then 0 else 1) := by fin_cases f <;> rfl
    have fits : (Pointer.cable 0 0 deck[arg].chunk).fields ⟨0,1,1⟩
        (DescentRetainedRangeDigits.page f) < 2^bits := by
      rw [span]
      split <;> omega
    exact (field_read _ _ _ _ _ _ _ _ hit fits).trans (span _)
  · have off : mouth (actual G p) z (code a).val party arg = none :=
      List.getElem?_eq_none (Nat.le_of_not_gt live)
    rw [ite_eq_right (size ▸ live),field_missing _ _ _ _ _ _ _ off]; rfl

end
end Hierarchy.DescentOrdinaryBorn

end OAI
