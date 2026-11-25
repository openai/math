import OAI.LinearAlgebra.SpectralBooks.MaskDiagonal
import OAI.LinearAlgebra.SpectralBooks.SpectralDiagonal
import Mathlib.Data.Finset.Image

/-! # Partial diagonals at a finite placement

Grouping a diagonal along an injection assigns a single label at each site
of its image and a trivial slot elsewhere. Hence the prices of all subsets of
one finite placement can be read from its single normalized spectral point.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

section

open SiteTensor

namespace SiteTensor.Raw

/-- Grouping by an injection produces the common diagonal on its image. -/
theorem ofRaw_group_diagonal_eq_mask {J I : Type} {K : Type*} [Fintype I] [Nonempty I]
    [Fintype J] [Field K] (σ : J ↪ I) (S : Finset I)
    (hS : ∀ i, i ∈ S ↔ ∃ j, σ j = i) (α : Type) [Fintype α] :
    ofRaw ((diagonal J K α).group σ) = ofRaw (maskDiagonal K S α) := by
  classical
  let fiber (i : I) (h : i ∈ S) : {j : J // σ j = i} :=
    ⟨((hS i).mp h).choose, ((hS i).mp h).choose_spec⟩
  have unique (i : I) (a b : {j : J // σ j = i}) : a = b :=
    Subtype.ext (σ.injective (a.property.trans b.property.symm))
  let e (i : I) : ((j : {j : J // σ j = i}) → α) ≃ (i ∈ S → α) :=
    { toFun := fun x h ↦ x (fiber i h)
      invFun := fun x j ↦ x ((hS i).mpr ⟨j, j.property⟩)
      left_inv := fun x ↦ funext fun j ↦ congrArg x (unique i _ j)
      right_inv := fun _ ↦ rfl }
  apply ofRaw_eq_iff.mpr (reindex_equivalent e ?_)
  intro x
  simp only [Raw.group, Raw.diagonal, Raw.maskDiagonal, Crossing.basisTensor]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply propext
  constructor
  · intro hx
    funext i hi
    change x i (fiber i hi) = a
    obtain ⟨j, hj⟩ := fiber i hi
    subst i
    exact congrFun hx j
  · intro hx
    funext j
    have hj : σ j ∈ S := (hS _).mpr ⟨j,rfl⟩
    exact (congrArg (x _) (unique _ _ (fiber _ hj))).trans (congrFun (congrFun hx _) hj)

end SiteTensor.Raw

namespace SpectralPlacementPrices

variable {K X : Type*} [Field K] [PseudoMetricSpace X]

theorem diagonal_nonneg (P : SpectralPlacementPrices K X) (S : Finset X) : 0 ≤ P.diagonal S := by
  classical
  by_cases h : S.Nonempty
  · simp only [diagonal, h, ite_true]
    let i : Fin S.card := ⟨0, Finset.card_pos.mpr h⟩
    simpa only [dist_self] using P.dist_le_diagonal
      (fun j : Fin S.card ↦ (S.equivFin.symm j).val) i i
  · simp [diagonal, h]

/-- At an injective placement one point evaluates the prices of all of its
nonempty subsets. -/
theorem exists_point_diagonal_map (P : SpectralPlacementPrices K X) {I : Type}
    [Fintype I] [Nontrivial I] (x : I ↪ X) :
    ∃ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop),
      ∃ c : ℝ, 0 ≤ c ∧ ∀ (S : Finset I), S.Nonempty →
        P.diagonal (S.map x) =
          c * Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal K S (Fin 2))) : ℝ) := by
  classical
  obtain ⟨φ, hφ⟩ := P.normalized x
  let c := P.price (Raw.diagonal I K (Fin 2)) x
  have hc : 0 ≤ c := by
    let i := Classical.arbitrary I
    simpa only [dist_self] using P.dist_le_diagonal x i i
  refine ⟨φ, c, hc, ?_⟩
  intro S hS
  let σ : S ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  have hs (i : I) : i ∈ S ↔ ∃ j, σ j = i := by
    constructor
    · intro hi
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.property
  have hocc : Finset.univ.image (x ∘ σ) = S.map x := by
    ext y
    simp [σ, Function.comp_def]
  let _ : Nonempty S := hS.to_subtype
  have hd : (Raw.diagonal S K (Fin 2)).coeff ≠ 0 := by
    obtain ⟨s,hs'⟩ := hS
    intro hz
    have he (a : Fin 2) : ((fun _ : S ↦ (0 : Fin 2)) = fun _ ↦ a) ↔ a = 0 :=
      ⟨fun h ↦ (congrFun h ⟨s,hs'⟩).symm, by rintro rfl; rfl⟩
    have h : (Raw.diagonal S K (Fin 2)).coeff (fun _ ↦ (0 : Fin 2)) = 0 :=
      congrFun hz _
    simp [Raw.diagonal, he] at h
  rw [← hocc, ← P.price_binaryDiagonal_eq, P.group, hφ _ ((Raw.group_ne_zero_iff _ _).mpr hd),
    Raw.ofRaw_group_diagonal_eq_mask σ S hs]

end SpectralPlacementPrices

end

end

end SpectralBooks
end LinearAlgebra
end OAI
