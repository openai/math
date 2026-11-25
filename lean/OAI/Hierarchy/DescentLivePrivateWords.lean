import OAI.Hierarchy.DescentKernelHistory
import Mathlib.Logic.Equiv.Prod

namespace OAI
/-! # Suppressing unused summation words without losing their field multiplicity -/

namespace Hierarchy.DescentKernelHistory.Recipe
open scoped Classical BigOperators
noncomputable section
variable {Tag B F : Type} [CommSemiring F] (r : Recipe Tag B)

def Used (i : r.Hidden) := ∃ v j,r.operand v j=.inr i
abbrev UsedWord := {i : r.Hidden //r.Used i}
abbrev DeadWord := {i : r.Hidden //¬r.Used i}

def activePort (v : r.Node) (j : Fin (r.arity v)) : B⊕r.UsedWord :=
  match h : r.operand v j with
  | .inl b=>.inl b
  | .inr a=>.inr ⟨a,v,j,h⟩

theorem activePort_read (v : r.Node) (j : Fin (r.arity v)) :
    (r.activePort v j).map id Subtype.val=r.operand v j := by
  unfold activePort
  split <;> rename_i h <;> simp only [Sum.map_inl,Sum.map_inr,id_eq] <;> exact h.symm

def restricted : Recipe Tag B where
  Hidden:=r.UsedWord
  width i:=r.width i.val
  Node:=r.Node
  tag:=r.tag
  arity:=r.arity
  operand:=r.activePort

def deadBits := ∑i : r.DeadWord,r.width i.val

set_option maxHeartbeats 950000 in
/-- The dead-word multiplicity is valid over an arbitrary field, including characteristic two. -/
theorem factor_value (scalar : Tag→List (List Bool)→F) (x : B→List Bool) :
    r.value scalar x=(2:F)^r.deadBits*r.restricted.value scalar x := by
  let L := (i : r.UsedWord)→Word (r.width i.val)
  let D := (i : r.DeadWord)→Word (r.width i.val)
  let live (h : L) := ∏v : r.Node,scalar (r.tag v)
    (List.ofFn fun j=>(r.activePort v j).elim x (fun i=>wordList (h i)))
  let split := Equiv.piEquivPiSubtypeProd r.Used (fun i=>Word (r.width i))
  have sum : r.value scalar x=∑t : L×D,live t.1 := by
    apply Fintype.sum_equiv split
    intro h
    apply Finset.prod_congr rfl
    intro v _
    apply congrArg (scalar (r.tag v))
    apply congrArg List.ofFn
    funext j
    rw [←r.activePort_read v j]
    cases r.activePort v j <;> rfl
  have card : Fintype.card D=2^r.deadBits := by
    simp [D,Word,deadBits,Fintype.card_pi,Finset.prod_pow_eq_pow_sum]
  have rest : r.restricted.value scalar x=∑t : L,live t := by
    unfold Recipe.value live
    apply Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
    intro t _
    apply Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
    intro v _
    rfl
  rw [sum,Fintype.sum_prod_type,rest]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  simp [card,nsmul_eq_mul]

/-- Every surviving private word has at least one distinct operand slot. -/
theorem used_le_slots : Fintype.card r.UsedWord≤∑v,r.arity v := by
  let slot : r.UsedWord→Σv,Fin (r.arity v) := fun h=>
    ⟨h.property.choose,h.property.choose_spec.choose⟩
  have read (h : r.UsedWord) : r.operand (slot h).1 (slot h).2=.inr h.val :=
    h.property.choose_spec.choose_spec
  have inj : Function.Injective slot := by
    intro x y h
    exact Subtype.ext (Sum.inr.inj ((read x).symm.trans
      ((congrArg (fun t : Σv,Fin (r.arity v)=>r.operand t.1 t.2) h).trans (read y))))
  exact (Fintype.card_le_of_injective slot inj).trans_eq (by simp [Fintype.card_sigma])

theorem deadBits_le : r.deadBits≤∑i : r.Hidden,r.width i := by
  unfold deadBits
  rw [←Finset.sum_subtype (Finset.univ.filter (fun i=>¬r.Used i)) (fun i=>by simp) r.width]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end
end Hierarchy.DescentKernelHistory.Recipe

end OAI
