import OAI.Optimization.LinearProgramming.Elimination.Mask
import OAI.Optimization.LinearProgramming.Elimination.Solve

/-! Fixed-width normal equations after masking dependent columns. This version uses the
same determinant order for all candidates and all final coordinates. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open Matrix Module Submodule
open scoped Matrix BigOperators
variable {K : Type*} [Field K] {d m : ℕ}

/-- Multiplication by the masked Gram matrix as diagonal scaling plus an identity penalty
on discarded variables. -/
theorem maskGram_mulVec (G : Matrix (Fin d) (Fin d) K) (a x : Fin d → K) (i : Fin d) :
    (maskGram G a *ᵥ x) i = a i * (G *ᵥ (fun j => a j*x j)) i + (1-a i)*x i := by
  simp only [maskGram, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp [ite_mul]

/-- Extend a coefficient map by zero outside a chosen set of columns. -/
def extendCoeffs (s : Finset (Fin d)) (w : s → K) (j : Fin d) : K :=
  if h : j ∈ s then w ⟨j,h⟩ else 0

private theorem mulVec_extendCoeffs (A : Matrix (Fin m) (Fin d) K) (s : Finset (Fin d)) (w : s → K) :
    A *ᵥ extendCoeffs s w = (A.submatrix id ((↑) : s → Fin d)) *ᵥ w := by
  ext i
  have h := Finset.sum_attach_eq_sum_dite s (fun j : s => A i j * w j)
  simpa [Matrix.mulVec, dotProduct, extendCoeffs, Finset.univ_eq_attach] using h.symm

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- One fixed-size selection mask for every system of the given shape. -/
def basisMask (G : Matrix (Fin d) (Fin d) K) := scanMask G (List.finRange d)

theorem basisMask_span (A : Matrix (Fin m) (Fin d) K) :
    span K (A.col '' (basisMask (Aᵀ*A) : Set (Fin d))) = span K (Set.range A.col) := by
  apply le_antisymm (span_mono (Set.image_subset_range ..))
  apply span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact (scanMask_spec A (List.finRange d)).2 j (List.mem_finRange j)

/-- The static scan supplies a consistent solution supported on its selected columns. -/
theorem exists_basisMask_solution (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K)
    (hx : ∃ x, A *ᵥ x = b) :
    ∃ z : Fin d → K, A *ᵥ z = b ∧ ∀ j ∉ basisMask (Aᵀ*A), z j = 0 := by
  let s := basisMask (Aᵀ*A)
  let B := A.submatrix id ((↑) : s → Fin d)
  have hr : Set.range B.col = A.col '' (s : Set (Fin d)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i,hi⟩,rfl⟩
  have h : b ∈ LinearMap.range B.mulVecLin := by
    rw [Matrix.range_mulVecLin,hr,show span K (A.col '' (s : Set (Fin d))) = _ from basisMask_span A,
      ← Matrix.range_mulVecLin]
    exact hx
  obtain ⟨w,hw⟩ := h
  exact ⟨extendCoeffs s w,(mulVec_extendCoeffs A s w).trans hw,
    fun j hj => by simp [extendCoeffs, s, hj]⟩

/-- Solve a consistent rectangular system using square determinant queries all of order `d`.
The final comparison gives the rejection result on an inconsistent system. -/
def fixedSolve (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) : Option (Fin d → K) :=
  let G := tabulate (Aᵀ*A)
  let s := basisMask G
  let a := flag s
  let M := tabulate (maskGram G a)
  let rhs := tabulateVec fun j => a j * (Aᵀ *ᵥ b) j
  match solveSquare M rhs with
  | none => none
  | some x => if A *ᵥ x = b then some x else none

omit [IsStrictOrderedRing K] in
theorem fixedSolve_sound (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (x : Fin d → K)
    (h : fixedSolve A b = some x) : A *ᵥ x = b := by
  simp only [fixedSolve, tabulate_eq, tabulateVec_eq] at h
  split at h
  · contradiction
  · split at h <;> simp_all

/-- The chosen solution is uniquely characterized by the original equations and zero
coordinates outside the descending greedy column basis. -/
theorem fixedSolve_of_supported (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (z : Fin d → K)
    (hz : A *ᵥ z=b) (hz0 : ∀j ∉ basisMask (Aᵀ*A), z j=0) : fixedSolve A b=some z := by
  let G := Aᵀ * A
  let s := basisMask G
  let M := maskGram G (flag s)
  change ∀ j ∉ s, z j = 0 at hz0
  have hli : LinearIndepOn K A.col (s : Set (Fin d)) := (scanMask_spec A (List.finRange d)).1
  have hm : M.det ≠ 0 := by simpa [M,G] using (maskGram_det_ne_zero_iff A s).2 hli
  have hzx : (fun j => (flag s j : K) * z j) = z := by
    funext j
    by_cases hj : j ∈ s
    · simp [flag,hj]
    · simp [flag,hj,hz0 j hj]
  have hvec : M *ᵥ z = fun j => flag s j * (Aᵀ *ᵥ b) j := by
    funext j
    rw [show (M *ᵥ z) j = _ from maskGram_mulVec G (flag s) z j, hzx]
    have hGz : G *ᵥ z = Aᵀ *ᵥ b := by rw [← hz,Matrix.mulVec_mulVec]
    rw [hGz]
    by_cases hj : j ∈ s
    · simp [flag,hj]
    · simp [flag,hj,hz0 j hj]
  have hsolve := solveSquare_mulVec M z hm
  simp only [fixedSolve,tabulate_eq,tabulateVec_eq]
  change (match solveSquare M (fun j => flag s j * (Aᵀ *ᵥ b) j) with
    | none => none | some x => if A *ᵥ x = b then some x else none) = some z
  rw [← hvec,hsolve]
  exact ite_eq_left hz

theorem fixedSolve_complete (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K)
    (hx : ∃ x, A *ᵥ x = b) : ∃ x, fixedSolve A b = some x := by
  obtain ⟨z,hz,hz0⟩ := exists_basisMask_solution A b hx
  exact ⟨z,fixedSolve_of_supported A b z hz hz0⟩

end Elimination
end LinearProgramming
end Optimization
end OAI
