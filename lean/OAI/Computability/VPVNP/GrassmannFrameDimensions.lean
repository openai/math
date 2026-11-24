import OAI.Computability.VPVNP.GrassmannFrameValue
import OAI.Computability.VPVNP.GrassmannTypes

/-!
# Dimensions of completed frame blocks

In the frame description of the binary Grassmannian, the two planes share
all completion columns. Their sum contains exactly the completion and both
original blocks. Independence counts the dimensions of all three spans.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open Set Submodule

variable {K V ι κ α : Type*} [Field K] [AddCommGroup V] [Module K V]

omit [AddCommGroup V] in
private theorem range_sumElim (v : ι → V) (w : κ → V) :
    range (Sum.elim v w) = range v ∪ range w := by
  simpa only [Set.image_univ, Set.preimage_univ] using Set.image_sumElim Set.univ v w

/-- Selecting columns by an injective map gives their count plus the
number of common completion columns as the dimension of the completed block. -/
theorem finrank_completedBlock_range [Fintype α] [Fintype κ] (v : ι → V) (w : κ → V)
    (f : α → ι) (hf : Function.Injective f)
    (h : LinearIndependent K (Sum.elim v w)) :
    Module.finrank K (completedBlock (K := K) v w (range f)) = Fintype.card α + Fintype.card κ := by
  have hi : LinearIndependent K (Sum.elim (v ∘ f) w) := by
    have hcomp := h.comp (Sum.map f (id : κ → κ)) (hf.sumMap Function.injective_id)
    convert hcomp using 1
    funext j
    cases j <;> rfl
  rw [completedBlock, ← range_comp, sup_comm, ← span_union, ← range_sumElim,
    finrank_span_eq_card hi, Fintype.card_sum]

variable {r s m : ℕ}

/-- Dimension of the completed first block of an independent frame. -/
theorem finrank_leftBlock (v : Fin (r + r) → V) (w : Fin s → V)
    (h : LinearIndependent K (Sum.elim v w)) :
    Module.finrank K (completedBlock (K := K) v w (leftIndices r)) = r + s := by
  unfold leftIndices
  simpa only [Fintype.card_fin] using finrank_completedBlock_range v w (Fin.castAdd r)
    (Fin.castAdd_injective _ _) h

/-- Dimension of the completed second block of an independent frame. -/
theorem finrank_rightBlock (v : Fin (r + r) → V) (w : Fin s → V)
    (h : LinearIndependent K (Sum.elim v w)) :
    Module.finrank K (completedBlock (K := K) v w (rightIndices r)) = r + s := by
  unfold rightIndices
  simpa only [Fintype.card_fin] using finrank_completedBlock_range v w (Fin.natAdd r)
    (Fin.natAdd_injective _ _) h

private theorem frameIndices_union (r : ℕ) : leftIndices r ∪ rightIndices r = univ := by
  apply Set.eq_univ_of_forall
  exact Fin.addCases (fun i ↦ Or.inl (mem_range_self i)) (fun i ↦ Or.inr (mem_range_self i))

/-- The sum of the two completed blocks spans the full frame. -/
theorem sup_frameBlocks (v : Fin (r + r) → V) (w : Fin s → V) :
    (completedBlock v w (leftIndices r) : Submodule K V) ⊔ completedBlock v w (rightIndices r) =
      span K (range (Sum.elim v w)) := by
  rw [completedBlock, completedBlock, sup_sup_sup_comm, sup_idem, ← span_union,
    ← Set.image_union, frameIndices_union, Set.image_univ, range_sumElim, span_union, sup_comm]

/-- Dimension of the sum of the two blocks, with their common completion
counted once. -/
theorem finrank_sup_frameBlocks (v : Fin (r + r) → V) (w : Fin s → V)
    (h : LinearIndependent K (Sum.elim v w)) :
    Module.finrank K (completedBlock v w (leftIndices r) ⊔ completedBlock v w (rightIndices r) :
      Submodule K V) = (r + r) + s := by
  rw [sup_frameBlocks, finrank_span_eq_card h, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

/-- The middle-dimensional plane spanned by the first block and the completion. -/
def leftPlane (v : Fin (r + r) → Space m) (w : Fin s → Space m) (hm : s + r = m)
    (h : LinearIndependent (ZMod 2) (Sum.elim v w)) : Plane m :=
  ⟨completedBlock (K := ZMod 2) v w (leftIndices r), (finrank_leftBlock v w h).trans ((Nat.add_comm r s).trans hm)⟩

/-- The middle-dimensional plane spanned by the second block and the completion. -/
def rightPlane (v : Fin (r + r) → Space m) (w : Fin s → Space m) (hm : s + r = m)
    (h : LinearIndependent (ZMod 2) (Sum.elim v w)) : Plane m :=
  ⟨completedBlock (K := ZMod 2) v w (rightIndices r), (finrank_rightBlock v w h).trans ((Nat.add_comm r s).trans hm)⟩

/-- The two planes of a completed independent frame have Grassmann type `r`. -/
theorem hasType_framePlanes (v : Fin (r + r) → Space m) (w : Fin s → Space m) (hm : s + r = m)
    (h : LinearIndependent (ZMod 2) (Sum.elim v w)) :
    HasType r (leftPlane v w hm h) (rightPlane v w hm h) :=
  (finrank_sup_frameBlocks v w h).trans (show (r + r) + s = m + r by omega)

end Grassmann

end VPVNP
end Computability
end OAI
