import OAI.Optimization.LinearProgramming.Elimination.Basic

/-! Fixed-size Gram tests for adaptive basis extraction. A column which is switched off
becomes a private unit vector at a new coordinate. This lets every branch use a determinant
of the same order and a table layout determined entirely by the input dimensions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open Matrix Module Submodule
open scoped Matrix BigOperators
variable {K : Type*} {m d : ℕ}

/-- Replace inactive columns by distinct unit vectors in fresh coordinates. -/
def padded [Zero K] [One K] (A : Matrix (Fin m) (Fin d) K) (s : Finset (Fin d)) :
    Matrix (Fin m ⊕ Fin d) (Fin d) K := Matrix.of fun i j => match i with
  | .inl p => if j ∈ s then A p j else 0
  | .inr p => if j ∈ s then 0 else (Pi.single p 1 : Fin d → K) j

variable [Field K]

private theorem padded_top (A : Matrix (Fin m) (Fin d) K) (s : Finset (Fin d))
    (x : Fin d → K) (i : Fin m) : (padded A s *ᵥ x) (.inl i) = (∑ j ∈ s, x j • A.col j) i := by
  simp [padded, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm, Matrix.col]

private theorem padded_bottom (A : Matrix (Fin m) (Fin d) K) (s : Finset (Fin d))
    (x : Fin d → K) (i : Fin d) : (padded A s *ᵥ x) (.inr i) = if i ∈ s then 0 else x i := by
  change (∑ j, (if j ∈ s then 0 else (Pi.single i 1 : Fin d → K) j) * x j) = _
  rw [Finset.sum_eq_single i]
  · by_cases h : i ∈ s <;> simp [h]
  · intro k _ hki
    by_cases h : k ∈ s <;> simp [h, Pi.single_eq_of_ne hki]
  · simp

private theorem padded_injective_iff (A : Matrix (Fin m) (Fin d) K) (s : Finset (Fin d)) :
    Function.Injective (padded A s).mulVec ↔ LinearIndepOn K A.col (s : Set (Fin d)) := by
  change Function.Injective (padded A s).mulVecLin ↔ _
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot', linearIndepOn_finset_iff]
  constructor
  · intro h u hu j hj
    let x := fun i => if i ∈ s then u i else 0
    have hs : (∑ i ∈ s, x i • A.col i) = 0 := by
      rw [← hu]
      exact Finset.sum_congr rfl fun i hi => by simp [x, hi]
    have hx : (padded A s).mulVecLin x = 0 := by
      ext i
      rcases i with i | i
      · change (padded A s *ᵥ x) (.inl i) = 0
        rw [padded_top, hs]; rfl
      · by_cases hi : i ∈ s <;> simp [padded_bottom, hi, x]
    simpa [x, hj] using congrFun (h x hx) j
  · intro h x hx
    change (padded A s *ᵥ x) = 0 at hx
    have hs : (∑ i ∈ s, x i • A.col i) = 0 := by
      ext i
      simpa only [padded_top, Pi.zero_apply] using congrFun hx (.inl i)
    funext i
    by_cases hi : i ∈ s
    · exact h x hs i hi
    · simpa only [padded_bottom, ite_eq_right hi, Pi.zero_apply] using congrFun hx (.inr i)

/-- A zero/one mask can be evaluated arithmetically. The full Gram table can be computed
once; subsequent tests change only the mask scalars. -/
def maskGram (G : Matrix (Fin d) (Fin d) K) (a : Fin d → K) :
    Matrix (Fin d) (Fin d) K := Matrix.of fun i j =>
  a i * a j * G i j + if i = j then (1-a i) else 0

def flag (s : Finset (Fin d)) (i : Fin d) : K := if i ∈ s then 1 else 0

private theorem unit_dot (i j : Fin d) :
    (∑ k, (Pi.single k 1 : Fin d → K) i * (Pi.single k 1 : Fin d → K) j) = if i=j then 1 else 0 := by
  rw [Finset.sum_eq_single i]
  · by_cases h : i=j
    · subst j; simp
    · simp [h]
  · intro k _ hki; simp [Pi.single_eq_of_ne hki.symm]
  · simp

theorem padded_gram_eq (A : Matrix (Fin m) (Fin d) K) (s : Finset (Fin d)) :
    (padded A s)ᵀ * padded A s = maskGram (Aᵀ * A) (flag s) := by
  ext i j
  by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
  · simp [padded, maskGram, flag, hi, hj, Matrix.mul_apply, Fintype.sum_sum_type]
  · have hne : i ≠ j := fun h => hj (h ▸ hi)
    simp [padded, maskGram, flag, hi, hj, hne, Matrix.mul_apply, Fintype.sum_sum_type]
  · have hne : i ≠ j := fun h => hi (h ▸ hj)
    simp [padded, maskGram, flag, hi, hj, hne, Matrix.mul_apply, Fintype.sum_sum_type]
  · simp [padded, maskGram, flag, hi, hj, Matrix.mul_apply, Fintype.sum_sum_type, unit_dot]

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- The test always uses a `d × d` determinant even though the active basis size changes. -/
theorem maskGram_det_ne_zero_iff (A : Matrix (Fin m) (Fin d) K) (s : Finset (Fin d)) :
    determinant (maskGram (Aᵀ * A) (flag s)) ≠ 0 ↔ LinearIndepOn K A.col (s : Set (Fin d)) := by
  rw [← padded_gram_eq, ← padded_injective_iff, determinant_eq, ← isUnit_iff_ne_zero,
    ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  change Function.Injective ((padded A s)ᵀ * padded A s).mulVecLin ↔ Function.Injective (padded A s).mulVecLin
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_transpose_mul_self]

/-- Scan the planned probes with an already computed square Gram matrix. -/
def scanMask (G : Matrix (Fin d) (Fin d) K) : List (Fin d) → Finset (Fin d)
  | [] => ∅
  | j :: js =>
    let s := scanMask G js
    let t := insert j s
    if determinant (maskGram G (flag t)) = 0 then s else t

theorem scanMask_spec (A : Matrix (Fin m) (Fin d) K) (js : List (Fin d)) :
    let s := scanMask (Aᵀ * A) js
    LinearIndepOn K A.col (s : Set (Fin d)) ∧
      ∀ i ∈ js, A.col i ∈ span K (A.col '' (s : Set (Fin d))) := by
  induction js with
  | nil => simp [scanMask]
  | cons j js ih =>
    let s := scanMask (Aᵀ * A) js
    let t := insert j s
    have hi : LinearIndepOn K A.col (s : Set (Fin d)) := ih.1
    by_cases h : determinant (maskGram (Aᵀ * A) (flag t)) = 0
    · have hs : scanMask (Aᵀ * A) (j::js) = s := ite_eq_left h
      rw [hs]
      refine ⟨hi, ?_⟩
      intro i hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · apply hi.mem_span_iff.mpr
        intro hplus
        exfalso
        exact (maskGram_det_ne_zero_iff A t).2 (by simpa [t] using hplus) h
      · exact ih.2 i hmem
    · have hs : scanMask (Aᵀ * A) (j::js) = t := ite_eq_right h
      rw [hs]
      refine ⟨(maskGram_det_ne_zero_iff A t).1 h, ?_⟩
      intro i hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact subset_span (Set.mem_image_of_mem _ (Finset.mem_insert_self _ s))
      · apply span_mono (Set.image_mono (show (s : Set (Fin d)) ⊆ t from Finset.subset_insert j s))
        exact ih.2 i hmem

end Elimination
end LinearProgramming
end Optimization
end OAI
