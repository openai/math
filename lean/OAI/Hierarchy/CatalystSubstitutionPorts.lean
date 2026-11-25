import OAI.Hierarchy.Catalyst

namespace OAI
/-! # Direction-wise packing of old and replacement catalyst ports -/

noncomputable section
namespace Hierarchy.CatalystSubstitution
open Catalyst
open scoped Classical

variable {k p : ℕ} (b c : Fin k → ℕ)

/-- The two banks occupy consecutive slots in each direction. -/
def wireEquiv : Wire b ⊕ Wire c ≃ Wire (fun j => b j + c j) where
  toFun := Sum.elim (fun w => ⟨w.1, finSumFinEquiv (Sum.inl w.2)⟩)
    (fun w => ⟨w.1, finSumFinEquiv (Sum.inr w.2)⟩)
  invFun := fun ⟨j,t⟩ => Sum.map (fun u => ⟨j,u⟩) (fun u => ⟨j,u⟩) (finSumFinEquiv.symm t)
  left_inv := by
    rintro (⟨j,t⟩ | ⟨j,t⟩)
    · exact congrArg (Sum.map (fun u => (⟨j,u⟩ : Wire b)) (fun u => (⟨j,u⟩ : Wire c)))
        ((finSumFinEquiv (m:=b j) (n:=c j)).symm_apply_apply (.inl t))
    · exact congrArg (Sum.map (fun u => (⟨j,u⟩ : Wire b)) (fun u => (⟨j,u⟩ : Wire c)))
        ((finSumFinEquiv (m:=b j) (n:=c j)).symm_apply_apply (.inr t))
  right_inv := by
    rintro ⟨j,t⟩
    obtain ⟨u,rfl⟩ := (finSumFinEquiv (m:=b j) (n:=c j)).surjective t
    cases u <;> simp

def oldPort : Port p b → Port p (fun j => b j + c j)
  | .inl i => .inl i
  | .inr (w,s) => .inr (wireEquiv b c (.inl w),s)

def newPort : Wire c × Bool → Port p (fun j => b j + c j)
  | (w,s) => .inr (wireEquiv b c (.inr w),s)

/-- Permutations of ports used when the replacement catalyst passes through. -/
def portEquiv : Port p b ⊕ (Wire c × Bool) ≃ Port p (fun j => b j + c j) :=
  (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumProdDistrib _ _ _).symm.trans (Equiv.prodCongr (wireEquiv b c) (Equiv.refl _))))

@[simp] theorem portEquiv_inl (i : Port p b) : portEquiv b c (.inl i) = oldPort b c i := by
  rcases i with i | ⟨w,s⟩ <;> rfl
@[simp] theorem portEquiv_inr (i : Wire c × Bool) : portEquiv (p:=p) b c (.inr i) = newPort b c i := rfl

/-- Permutation when the old catalyst passes through and the new bank is local. -/
def flippedEquiv : Port p c ⊕ (Wire b × Bool) ≃ Port p (fun j => b j + c j) :=
  (Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
    ((Equiv.sumAssoc _ _ _).symm.trans (portEquiv b c)))

@[simp] theorem flipped_inl_data (i : Fin p) : flippedEquiv b c (.inl (.inl i)) = .inl i := rfl
@[simp] theorem flipped_inl_wire (i : Wire c × Bool) :
    flippedEquiv (p:=p) b c (.inl (.inr i)) = newPort b c i := rfl
@[simp] theorem flipped_inr (i : Wire b × Bool) :
    flippedEquiv (p:=p) b c (.inr i) = oldPort b c (.inr i) := rfl

end Hierarchy.CatalystSubstitution

end
end OAI
