import OAI.Hierarchy.DescentSparseWordOrder
import OAI.Hierarchy.DescentBinaryContact

namespace OAI
/-! # Equivalence between the sorted cable layout and the former abstract bit ordering -/

namespace Hierarchy.DescentOrderedWords
open DescentContactTree.Physical
open scoped BigOperators Classical
noncomputable section
variable {I : Type*} [Fintype I] {N : ℕ} (key : I ↪ Fin N) (width : I→ℕ)

def decode : (Fin (∑i,width i)→Bool) ≃ ((i : I)→Fin (width i)→Bool) :=
  (Equiv.arrowCongr (address key width).symm (Equiv.refl _)).trans (Equiv.piCurry (fun _ _=>Bool))

@[simp] theorem read (x : Fin (∑i,width i)→Bool) (i : I) (j : Fin (width i)) :
    decode key width x i j=x (bitIndex key width ⟨i,j⟩) := rfl

/-- The physical word permutation maps a legacy bit address to the ordered
one holding precisely the same original item/bit. The implementation of the
ordered decoder itself uses only the explicit sparse keys. -/
def permutation : Equiv.Perm (Fin (∑i,width i)) :=
  ((Fintype.equivFin (Σi,Fin (width i))).trans (finCongr (by simp))).symm.trans (address key width)

theorem decode_eq (word : Fin (∑i,width i)→Bool) :
    decode key width word=concat width (word ∘ permutation key width) := by
  funext i j
  let chosen := (Fintype.equivFin (Σi,Fin (width i))).trans (finCongr (show Fintype.card (Σi,Fin (width i))=∑i,width i by simp))
  change word (address key width ⟨i,j⟩)=word (address key width (chosen.symm (chosen ⟨i,j⟩)))
  rw [Equiv.symm_apply_apply]

theorem encode_eq (x : (i:I)→Fin (width i)→Bool) :
    (decode key width).symm x ∘ permutation key width=(concat width).symm x := by
  apply (concat width).injective
  rw [←decode_eq,Equiv.apply_symm_apply,Equiv.apply_symm_apply]

end
end Hierarchy.DescentOrderedWords

end OAI
