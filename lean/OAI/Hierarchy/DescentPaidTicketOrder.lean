import OAI.Hierarchy.DescentTerminalMatrix
import OAI.Hierarchy.DescentOrderedOffsetTable

namespace OAI
/-! # Chronological numbering of the original bundles of a direct contact -/

namespace Hierarchy.DescentBaseProfile
open DescentOrderedWords
open scoped BigOperators Classical
noncomputable section
variable {E C : Type*} [Fintype E] [Fintype C] {L : ℕ} (key : E↪Fin L) (label : E→C)

def ordinalKey (c : C) : {e // label e=c} ↪ Fin L := (Function.Embedding.subtype _).trans key

def ordinalOf (c : C) : {e // label e=c} ≃ Fin (contactCounts label c) :=
  let unit : {e // label e=c} ≃ (Σ _: {e // label e=c},Fin 1) := {
    toFun := fun e=>⟨e,0⟩
    invFun := Sigma.fst
    left_inv := fun _=>rfl
    right_inv := by rintro ⟨e,j⟩; exact congrArg (Sigma.mk e) (Subsingleton.elim _ _) }
  (unit.trans (address (ordinalKey key label c) (fun _=>1))).trans
    (finCongr (by simp [Fintype.card_subtype,contactCounts]))

def orderedIndex : E ≃ Σ c,Fin (contactCounts label c) :=
  (Equiv.sigmaFiberEquiv label).symm.trans (Equiv.sigmaCongrRight (ordinalOf key label))

omit [Fintype C] in
@[simp] theorem orderedIndex_label (e : E) : (orderedIndex key label e).1=label e := rfl

omit [Fintype C] in
theorem orderedIndex_read (e : E) :
    (orderedIndex key label e).2.val=(Finset.univ.filter fun x=>key x<key e ∧ label x=label e).card := by
  change offset (ordinalKey key label (label e)) (fun _=>1) ⟨e,rfl⟩+0=_
  rw [Nat.add_zero]
  change offset ((Function.Embedding.subtype (fun j=>label j=label e)).trans key) (fun _=>1) ⟨e,rfl⟩=_
  rw [fibre_offset label (fun _=>1) key]
  simp only [offset,before,Finset.sum_filter,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases lt : key j<key e <;> by_cases tag : label j=label e <;> simp [lt,tag]

end
end Hierarchy.DescentBaseProfile

end OAI
