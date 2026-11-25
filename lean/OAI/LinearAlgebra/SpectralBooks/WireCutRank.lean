import OAI.LinearAlgebra.SpectralBooks.CutSpectrum
import OAI.LinearAlgebra.SpectralBooks.RawLogPrice

/-! # Matrix rank of a wire across a cut -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical NNReal
noncomputable section

namespace Crossing

variable {I K : Type*} [Fintype I] [Field K] (s : I → Prop) [DecidablePred s]

/-- The cut matrix of a sum of basis tensors factors through a matrix index for
the labels of the summands. -/
theorem cutMatrix_rank_basisTensor_le {A : I → Type*} [∀ i, Fintype (A i)]
    {L : Type*} [Fintype L] (term : L → ∀ i, A i) :
    (cutMatrix s (basisTensor (F := K) term)).rank ≤ Fintype.card L := by
  classical
  let P : Matrix (∀ i : {i // s i}, A i) L K := fun x a ↦
    if x = (cutEquiv s A (term a)).1 then 1 else 0
  let Q : Matrix L (∀ i : {i // ¬ s i}, A i) K := fun a y ↦
    if y = (cutEquiv s A (term a)).2 then 1 else 0
  have fac : cutMatrix s (basisTensor (F := K) term) = P * Q := by
    ext x y
    simp only [Matrix.mul_apply, cutMatrix, basisTensor]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hx : x = (cutEquiv s A (term a)).1 <;>
      simp only [Equiv.symm_apply_eq, Prod.ext_iff, P, Q, hx] <;> simp
  rw [fac]
  exact (Matrix.rank_mul_le_left _ _).trans P.rank_le_card_width

namespace Wire

variable (e : Wire I)

private def sideTerm (a : Fin e.width → Bool) (j : {i // s i}) : e.Leg j :=
  e.basisTerm a j

omit [Fintype I] [DecidablePred s] in
private theorem sideTerm_injective (h : s e.left ∨ s e.right) :
    Function.Injective (sideTerm s e) := by
  intro a b he
  funext t
  rcases h with hl | hr
  · exact congrFun (congrFun he ⟨e.left, hl⟩) ⟨t, Or.inl rfl⟩
  · exact congrFun (congrFun he ⟨e.right, hr⟩) ⟨t, Or.inr rfl⟩

private theorem side_card_le_one (hl : ¬ s e.left) (hr : ¬ s e.right) :
    Fintype.card (∀ i : {i // s i}, e.Leg i) ≤ 1 := by
  apply Fintype.card_le_one_iff.mpr
  intro a b
  funext j t
  rcases t.property with h | h
  · exact (hl (h ▸ j.property)).elim
  · exact (hr (h ▸ j.property)).elim

/-- A wire on the same side of a cut has flattening rank one. A cut separating
the endpoints has one independent row and column for every bit string. -/
theorem cutMatrix_rank_basisTensor :
    (cutMatrix s (basisTensor (F := K) e.basisTerm)).rank =
      if (s e.left ↔ s e.right) then 1 else 2 ^ e.width := by
  classical
  let M := cutMatrix s (basisTensor (F := K) e.basisTerm)
  let row := sideTerm s e
  let col := sideTerm (fun i ↦ ¬ s i) e
  have entry (a b : Fin e.width → Bool) :
      M (row a) (col b) = ∑ c, if row a = row c ∧ col b = col c then 1 else (0 : K) := by
    simp only [M, cutMatrix, basisTensor]
    apply Finset.sum_congr rfl
    intro c _
    simp only [Equiv.symm_apply_eq, Prod.ext_iff]
    rfl
  have nz (a : Fin e.width → Bool) : M (row a) (col a) = 1 := by
    have inj (b : Fin e.width → Bool) : row a = row b ∧ col a = col b ↔ a = b := by
      constructor
      · rintro ⟨h, h'⟩
        by_cases hl : s e.left
        · exact sideTerm_injective s e (Or.inl hl) h
        · exact sideTerm_injective (fun i ↦ ¬s i) e (Or.inl hl) h'
      · rintro rfl
        exact ⟨rfl, rfl⟩
    simp [entry, inj]
  change M.rank = _
  split_ifs with same
  · apply le_antisymm
    · by_cases hl : s e.left
      · exact M.rank_le_card_width.trans (side_card_le_one (fun i ↦ ¬s i) e
          (not_not.mpr hl) (not_not.mpr (same.mp hl)))
      · exact M.rank_le_card_height.trans (side_card_le_one s e hl (hl ∘ same.mpr))
    · let a : Fin e.width → Bool := fun _ ↦ false
      have one : M.submatrix (fun _ : Unit ↦ row a) (fun _ : Unit ↦ col a) = 1 := by
        ext x y
        cases x
        cases y
        simpa [Matrix.one_apply, Matrix.submatrix] using nz a
      have h := M.rank_submatrix_le (fun _ : Unit ↦ row a) (fun _ : Unit ↦ col a)
      simpa [one] using h
  · have hr : Function.Injective row := sideTerm_injective s e (by tauto)
    have hc : Function.Injective col := sideTerm_injective (fun i ↦ ¬s i) e (by tauto)
    have diag : M.submatrix row col = 1 := by
      ext a b
      by_cases h : a = b
      · subst b
        simpa [Matrix.submatrix, Matrix.one_apply] using nz a
      · have off (c) : ¬(row a = row c ∧ col b = col c) :=
          fun hc' ↦ h ((hr hc'.1).trans (hc hc'.2).symm)
        simp [Matrix.submatrix, entry, off, h]
    apply le_antisymm
    · simpa using cutMatrix_rank_basisTensor_le (K := K) s e.basisTerm
    · simpa [diag] using M.rank_submatrix_le row col

open SiteTensor

/-- The width-bit equality tensor on the two endpoints, with scalar legs elsewhere. -/
def raw (K : Type*) [CommSemiring K] (e : Wire I) : Raw.{0} I K :=
  ⟨e.Leg, fun _ ↦ inferInstance, basisTensor e.basisTerm⟩

variable [Nonempty I] [Nonempty {i // s i}] [Nonempty {i // ¬s i}]

/-- A proper cut evaluates an internal wire to one and a crossing wire to its dimension. -/
theorem cutSpectrum_raw :
    (cutSpectrum s K).val (ofRaw (e.raw K)) =
      if (s e.left ↔ s e.right) then 1 else (2 : ℝ≥0) ^ e.width := by
  rw [cutSpectrum_ofRaw]
  change ((cutMatrix s (basisTensor (F := K) e.basisTerm)).rank : ℝ≥0) = _
  rw [cutMatrix_rank_basisTensor]
  split_ifs <;> simp

/-- The logarithmic cut price counts the number of bits crossing the cut at the given scale. -/
theorem rawLogPrice_cutSpectrum (c : ℝ) :
    rawLogPrice (cutSpectrum s K) c (e.raw K) =
      if (s e.left ↔ s e.right) then 0 else c * e.width := by
  rw [rawLogPrice, cutSpectrum_raw]
  split_ifs <;> simp [Real.logb_pow]

end Wire
end Crossing

end

end SpectralBooks
end LinearAlgebra
end OAI
