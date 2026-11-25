import OAI.Optimization.LinearProgramming.Farkas.Sparse
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Pi

/-! A finite-dimensional Farkas alternative by elimination over an ordered field. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Farkas

open Matrix

universe u v

variable {K : Type v} [Field K] [LinearOrder K]

/-- Keep zero-coefficient rows and combine each lower bound with each upper bound.
Inapplicable rows are identically zero. -/
private noncomputable def weights {ι : Type u} [DecidableEq ι] (a : ι → K) :
    Matrix (ι ⊕ (ι × ι)) ι K := Matrix.of fun row =>
  match row with
  | .inl i => if a i = 0 then Pi.single i 1 else 0
  | .inr (i, j) => if a i < 0 ∧ 0 < a j
      then Pi.single i (-(a i)⁻¹) + Pi.single j (a j)⁻¹ else 0

private theorem weights_inl {ι : Type u} [Fintype ι] [DecidableEq ι] (a r : ι → K) (i : ι) :
    (weights a *ᵥ r) (.inl i) = if a i = 0 then r i else 0 := by
  change (if a i = 0 then Pi.single i 1 else 0) ⬝ᵥ r = _
  split <;> simp_all

private theorem weights_inr {ι : Type u} [Fintype ι] [DecidableEq ι] (a r : ι → K) (i j : ι) :
    (weights a *ᵥ r) (.inr (i, j)) = if a i < 0 ∧ 0 < a j then r j / a j - r i / a i else 0 := by
  change (if a i < 0 ∧ 0 < a j then Pi.single i (-(a i)⁻¹) + Pi.single j (a j)⁻¹ else 0) ⬝ᵥ r = _
  split <;> simp_all [add_dotProduct, div_eq_mul_inv, mul_comm, sub_eq_neg_add]

variable [IsStrictOrderedRing K]

private theorem weights_nonneg {ι : Type u} [DecidableEq ι] (a : ι → K)
    (q : ι ⊕ (ι × ι)) (i : ι) : 0 ≤ weights a q i := by
  rcases q with j | ⟨j, k⟩
  · by_cases hj : a j = 0
    · have hjpos : (0 : ι → K) ≤ Pi.single j 1 := Pi.single_nonneg.mpr zero_le_one
      simpa [weights, hj] using hjpos i
    · simp [weights, hj]
  · by_cases h : a j < 0 ∧ 0 < a k
    · simp only [weights, Matrix.of_apply, h]
      apply add_nonneg
      · have hj : (0 : ι → K) ≤ Pi.single j (-(a j)⁻¹) := Pi.single_nonneg.mpr (neg_nonneg.mpr (inv_nonpos.mpr h.1.le))
        exact hj i
      · have hk : (0 : ι → K) ≤ Pi.single k (a k)⁻¹ := Pi.single_nonneg.mpr (inv_nonneg.mpr h.2.le)
        exact hk i
    · simp [weights, h]

omit [IsStrictOrderedRing K] in
private theorem weights_annihilate {ι : Type u} [Fintype ι] [DecidableEq ι] (a : ι → K) :
    weights a *ᵥ a = 0 := by
  funext q
  rcases q with i | ⟨i, j⟩
  · by_cases h : a i = 0 <;> simp [weights_inl, h]
  · by_cases h : a i < 0 ∧ 0 < a j
    · simp [weights_inr, h, h.1.ne, h.2.ne']
    · simp [weights_inr, h]

private theorem choose_coordinate {ι : Type u} [Fintype ι] [DecidableEq ι] (a r : ι → K)
    (h : 0 ≤ weights a *ᵥ r) : ∃ t, ∀ i, a i * t ≤ r i := by
  classical
  have hz (i : ι) (hi : a i = 0) : 0 ≤ r i := by simpa [weights_inl, hi] using h (.inl i)
  have hp (i j : ι) (hi : a i < 0) (hj : 0 < a j) : r i / a i ≤ r j / a j := by
    simpa [weights_inr, hi, hj, sub_nonneg] using h (.inr (i, j))
  let L := Finset.univ.filter fun i => a i < 0
  by_cases hn : L.Nonempty
  · obtain ⟨i, hi, hmax⟩ := L.exists_max_image (fun i => r i / a i) hn
    have ai : a i < 0 := (Finset.mem_filter.mp hi).2
    refine ⟨r i / a i, fun j => ?_⟩
    rcases lt_trichotomy (a j) 0 with hj | hj | hj
    · have hji := hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
      simpa [mul_comm] using (div_le_iff_of_neg hj).mp hji
    · simpa [hj] using hz j hj
    · simpa [mul_comm] using (le_div_iff₀ hj).mp (hp i j ai hj)
  · let bounds := insert 0 (Finset.univ.image fun i => r i / a i)
    have hne : bounds.Nonempty := Finset.insert_nonempty _ _
    refine ⟨bounds.min' hne, fun j => ?_⟩
    rcases lt_trichotomy (a j) 0 with hj | hj | hj
    · exact (hn ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩).elim
    · simpa [hj] using hz j hj
    · have hjb : r j / a j ∈ bounds := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      simpa [mul_comm] using (le_div_iff₀ hj).mp (bounds.min'_le _ hjb)

/-- An ordered-field alternative, including systems with no rows or no variables. -/
theorem alternative (d : ℕ) : ∀ (ι : Type u) [Fintype ι] (A : Matrix ι (Fin d) K) (b : ι → K),
    (∃ x, A *ᵥ x ≤ b) ∨ (∃ y, 0 ≤ y ∧ A.transpose *ᵥ y = 0 ∧ b ⬝ᵥ y < 0) := by
  classical
  induction d with
  | zero =>
    intro ι _ A b
    by_cases h : ∀ i, 0 ≤ b i
    · refine Or.inl ⟨0, fun i => ?_⟩
      simpa [Matrix.mulVec, dotProduct] using h i
    · obtain ⟨i, hni⟩ := not_forall.mp h
      have hi := lt_of_not_ge hni
      refine Or.inr ⟨Pi.single i 1, ?_, Subsingleton.elim _ _, ?_⟩
      · intro j
        simp only [Pi.zero_apply, Pi.single_apply]
        split <;> simp
      · simpa using hi
  | succ d ih =>
    intro ι _ A b
    let a : ι → K := fun i => A i 0
    let B : Matrix ι (Fin d) K := Matrix.of fun i j => A i j.succ
    let W := weights a
    rcases ih (ι ⊕ (ι × ι)) (W * B) (W *ᵥ b) with ⟨x, hx⟩ | ⟨z, hz, hB, hb⟩
    · have h : 0 ≤ W *ᵥ (b - B *ᵥ x) := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
        exact fun q => sub_nonneg.mpr (hx q)
      obtain ⟨t, ht⟩ := choose_coordinate a (b - B *ᵥ x) h
      refine Or.inl ⟨Fin.cons t x, fun i => ?_⟩
      change (∑ j, A i j * (Fin.cons t x : Fin (d+1) → K) j) ≤ b i
      rw [Fin.sum_univ_succ]
      exact (le_sub_iff_add_le).mp (ht i)
    · let y := W.transpose *ᵥ z
      have hy : 0 ≤ y := fun i => dotProduct_nonneg_of_nonneg (fun j => weights_nonneg a j i) hz
      have hzero : a ⬝ᵥ y = 0 := by
        change a ⬝ᵥ (W.transpose *ᵥ z) = 0
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, weights_annihilate, zero_dotProduct]
      have htail : B.transpose *ᵥ y = 0 := by
        rw [Matrix.transpose_mul] at hB
        simpa only [y, Matrix.mulVec_mulVec] using hB
      refine Or.inr ⟨y, hy, funext (Fin.cases hzero (fun j => congrFun htail j)), ?_⟩
      change b ⬝ᵥ (W.transpose *ᵥ z) < 0
      simpa only [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] using hb

/-- A negative certificate rules out every feasible point, over the same field. -/
theorem certificate_excludes_feasible {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ K) (b : ι → K) {y : ι → K} (hy : 0 ≤ y)
    (hA : A.transpose *ᵥ y = 0) (hb : b ⬝ᵥ y < 0) : ¬ ∃ x, A *ᵥ x ≤ b := by
  rintro ⟨x, hx⟩
  have h : 0 ≤ y ⬝ᵥ (b - A *ᵥ x) := dotProduct_nonneg_of_nonneg hy (fun i => sub_nonneg.mpr (hx i))
  rw [dotProduct_sub, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, zero_dotProduct,
    sub_zero, dotProduct_comm] at h
  exact (not_lt_of_ge h) hb

/-- The finite-dimensional alternative with the normalized sparse multiplier of §§2 and 8. -/
theorem sparse_alternative {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) :
    (∃ x, A *ᵥ x ≤ b) ∨
    (∃ y : Fin m → K, 0 ≤ y ∧ A.transpose *ᵥ y = 0 ∧ b ⬝ᵥ y = -1 ∧
      (Finset.univ.filter fun i => y i ≠ 0).card ≤ A.rank + 1) := by
  rcases alternative d (Fin m) A b with hx | ⟨y, hy, hA, hb⟩
  · exact Or.inl hx
  · exact Or.inr (sparse_certificate A b y hy hA hb)

end Farkas
end LinearProgramming
end Optimization
end OAI
