import OAI.LinearAlgebra.FiniteFourier.DiagonalShear

/-! # Words for additive padding and truncation

An embedding pairs each short-array register with its image in a longer array.
Constant scalar shears on the pairs implement signed padding and truncation.
All remaining registers keep their initial contents.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Matrix

variable {K : Type*} [CommRing K] {I J : Type} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

private theorem layerWord_partialPairs (e : I ↪ J) (u v : K) {d : ℕ}
    (h : LayerWord d (fromBlocks (1 : Matrix I I K) (diagonal fun _ => u)
        (diagonal fun _ => v) 1)) :
    LayerWord d (fromBlocks (1 : Matrix I I K)
      (u • (1 : Matrix J J K).submatrix e (Equiv.refl J))
      (v • (1 : Matrix J J K).submatrix (Equiv.refl J) e) 1) := by
  classical
  let C := {j : J // j ∉ Set.range e}
  let split : I ⊕ C ≃ J :=
    ((Equiv.ofInjective e e.injective).sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl _)
  let q : (I ⊕ I) ⊕ C ≃ I ⊕ J :=
    (Equiv.sumAssoc _ _ _).trans ((Equiv.refl _).sumCongr split)
  have h₀ (i : I) : q (.inl (.inl i)) = .inl i := rfl
  have h₁ (i : I) : q (.inl (.inr i)) = .inr (e i) := rfl
  have h₂ (j : C) : q (.inr j) = .inr j.val := rfl
  have hv (i : I) (j : C) : e i ≠ j.val := fun eq => j.prop ⟨i, eq⟩
  convert (layerWord_parallel h (layerWord_one (K := K) (I := C) d)).relabel q using 1
  ext i j
  obtain ⟨i, rfl⟩ := q.surjective i
  obtain ⟨j, rfl⟩ := q.surjective j
  simp only [submatrix_apply, Equiv.symm_apply_apply]
  rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
    simp [h₀, h₁, h₂, Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.submatrix, e.injective.eq_iff, hv, Ne.symm (hv _ _), Subtype.val_injective.eq_iff, smul_eq_mul,
      mul_ite]

/-- Signed padding needs only the word for a single scalar transvection. -/
theorem layerWord_add_padding_of_pair (e : I ↪ J) (c : K) {d : ℕ}
    (hc : LayerWord d (transvection (0 : Fin 2) 1 c)) :
    LayerWord d (fromBlocks (1 : Matrix I I K) 0
      (c • (1 : Matrix J J K).submatrix (Equiv.refl J) e) 1) := by
  have h := layerWord_diagShear_upper_of_pairs (fun _ : I => c) (fun _ => hc)
  have h' : LayerWord d (fromBlocks 1 0 (diagonal fun _ : I => c) 1) := by
    convert h.relabel (Equiv.sumComm I I) using 1
    ext (i | i) (j | j) <;> rfl
  simpa using layerWord_partialPairs e 0 c (by simpa using h')

/-- Signed truncation needs only the word for a single scalar transvection. -/
theorem layerWord_add_truncation_of_pair (e : I ↪ J) (c : K) {d : ℕ}
    (hc : LayerWord d (transvection (0 : Fin 2) 1 c)) :
    LayerWord d (fromBlocks (1 : Matrix J J K) 0
      (c • (1 : Matrix J J K).submatrix e (Equiv.refl J)) 1) := by
  have h := layerWord_diagShear_upper_of_pairs (fun _ : I => c) (fun _ => hc)
  have hp := layerWord_partialPairs e c 0 (by simpa using h)
  have hw := hp.relabel (Equiv.sumComm I J)
  simp only [zero_smul] at hw
  convert hw using 1
  ext (i | i) (j | j) <;> rfl

/-- Add the short array, scaled by `c`, into its image in the larger array. -/
theorem layerWord_add_padding {K : Type*} [Field K] (e : I ↪ J) (c : K) :
    LayerWord 3 (fromBlocks (1 : Matrix I I K) 0
      (c • (1 : Matrix J J K).submatrix (Equiv.refl J) e) 1) := by
  exact layerWord_add_padding_of_pair e c (layerWord_transvection (by decide) c)

/-- Add the selected entries of the longer array, scaled by `c`, into the shorter array. -/
theorem layerWord_add_truncation {K : Type*} [Field K] (e : I ↪ J) (c : K) :
    LayerWord 3 (fromBlocks (1 : Matrix J J K) 0
      (c • (1 : Matrix J J K).submatrix e (Equiv.refl J)) 1) := by
  exact layerWord_add_truncation_of_pair e c (layerWord_transvection (by decide) c)

end

end

end FiniteFourier
end LinearAlgebra
end OAI
