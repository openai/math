import OAI.Computability.NearSquareRoot.SynchronizedPlacedWord

/-! # Relabelling a parallel placement at its two boundaries -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix

variable {X Y J A P : Type}

/-- The local and physical address equivalences compose directly with an injective placement. -/
def placementRelabel (f : X ≃ Y) (g : A ≃ P) (e : Y × J ↪ P) : X × J ↪ A :=
  ((f.prodCongr (Equiv.refl J)).toEmbedding.trans e).trans g.symm.toEmbedding

theorem placementRelabel_apply (f : X ≃ Y) (g : A ≃ P) (e : Y × J ↪ P) (x : X) (j : J) :
    placementRelabel f g e (x,j) = g.symm (e (f x,j)) := rfl

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A] [Fintype P] [DecidableEq P]

/-- Conjugating the source and the target of a placed gate simply relabels its embedding. -/
theorem placeHom_relabel (f : X ≃ Y) (g : A ≃ P) (e : Y × J ↪ P) (U : Matrix X X ℂ) :
    (placeHom e (U.submatrix f.symm f.symm)).submatrix g g = placeHom (placementRelabel f g e) U := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  funext y
  rw [submatrix_mulVec_equiv]
  change ((placeHom e (U.submatrix f.symm f.symm)) *ᵥ (x ∘ g.symm)) (g y) =
      (placeHom (placementRelabel f g e) U *ᵥ x) y
  by_cases h : g y ∈ Set.range e
  · obtain ⟨⟨p,j⟩, hp⟩ := h
    obtain ⟨u,rfl⟩ := f.surjective p
    have hy : y = placementRelabel f g e (u,j) := g.injective (by simpa [placementRelabel_apply] using hp.symm)
    rw [hy, placeHom_mulVec U, (placementRelabel f g e).injective.extend_apply, placementRelabel_apply,
      g.apply_symm_apply, placeHom_mulVec, e.injective.extend_apply, submatrix_mulVec_equiv]
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm, placementRelabel_apply]
    rfl
  · have h' : y ∉ Set.range (placementRelabel f g e) := by
      rintro ⟨⟨p,j⟩, rfl⟩
      exact h ⟨(f p,j), by simp [placementRelabel_apply]⟩
    rw [placeHom_mulVec, Function.extend_apply' _ _ _ h, placeHom_mulVec, Function.extend_apply' _ _ _ h']
    simp

end ShortFourier

end NearSquareRoot
end Computability
end OAI
