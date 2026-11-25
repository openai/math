import OAI.Hierarchy.DescentOrdinaryRegisteredOperands
import OAI.Hierarchy.DescentPackedLocalAtoms

namespace OAI
/-! # A packed actor compaction selects the same donor in every operand column -/
namespace Hierarchy.DescentOperandStateBanks
open DescentSIMDLookup DescentPackedLocalAtoms
open scoped Classical
noncomputable section
variable {width count output : ℕ}

def TypedHeader (x : Fin 4 → Cell width) := ∃p : Pointer,∀f,(x f).val=p.header f

theorem typed_zero : TypedHeader (fun _ => (0 : Cell width)) := by
  refine ⟨.privateWord 0,?_⟩
  intro f
  fin_cases f <;> rfl

/-- The provenance of all columns, including span coordinates, agrees at every
destination, even when the actor book has a hole or there are no source rows. -/
theorem packed_donor {α : Type*} (mask : Cell (1*count)) (records : α → Fin count → Cell width)
    (j : Fin output) :
    (∃u : Fin count,((encode 1 count).symm mask u≠0 ∧
      earlier ((encode 1 count).symm mask) u=j.val) ∧
      ∀f,(encode width output).symm (pack width count output mask (encode width count (records f))) j=records f u) ∨
    ∀f,(encode width output).symm (pack width count output mask (encode width count (records f))) j=0 := by
  let bit:=(encode 1 count).symm mask
  by_cases h : ∃u : Fin count,bit u≠0 ∧ earlier bit u=j.val
  · obtain ⟨u,live,at_⟩:=h
    refine Or.inl ⟨u,⟨live,at_⟩,fun f => ?_⟩
    simpa only [pack,Equiv.symm_apply_apply] using field_at bit (records f) u live j at_
  · refine Or.inr (fun f => ?_)
    simp only [pack,Equiv.symm_apply_apply,field]
    exact dite_eq_right h

theorem typed_packed (mask : Cell (1*count)) (records : Fin 4→Fin count→Cell width)
    (typed : ∀u,TypedHeader (fun f=>records f u)) (j : Fin output) :
    TypedHeader (fun f => (encode width output).symm
      (pack width count output mask (encode width count (records f))) j) := by
  rcases packed_donor mask records j with ⟨u,_,selected⟩ | blank
  · obtain ⟨p,valid⟩:=typed u
    exact ⟨p,fun f => (congrArg Fin.val (selected f)).trans (valid f)⟩
  · obtain ⟨p,valid⟩:=typed_zero (width:=width)
    exact ⟨p,fun f => (congrArg Fin.val (blank f)).trans (valid f)⟩

end
end Hierarchy.DescentOperandStateBanks


namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentOperandStateBanks DescentOrdinaryAtomFieldRAM.ScalarOperand
variable {l : Layout}

theorem books_typed_iff (b : Books l) : BookPointers b ↔
    ∀bl node arg h g,TypedHeader (fun f=>take node (b bl (DescentPriorOperandColumns.pageOf arg f) h g)) := by
  constructor
  · intro all bl node arg h g
    obtain ⟨p,read⟩ := all (l.index (bl,node,arg)) h g
    refine ⟨p, fun f => ?_⟩
    simpa only [booksHeader, Equiv.symm_apply_apply] using read f
  · intro every j h g
    exact every (l.index.symm j).1 (l.index.symm j).2.1 (l.index.symm j).2.2 h g

end Hierarchy.DescentDatedPriorOperand

end OAI
