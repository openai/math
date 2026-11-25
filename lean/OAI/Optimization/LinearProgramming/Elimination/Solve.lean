import OAI.Optimization.LinearProgramming.Elimination.Basic

/-! Cramer's rule on the independent columns recovers an exact solution of any consistent
rectangular system, over its original ordered field. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open Matrix Module Submodule
open scoped Matrix BigOperators

variable {K : Type*} {m d r : ℕ}

/-- Materialize a vector once before its coordinates are used several times. -/
def tabulateVec (w : Fin d → K) : Fin d → K :=
  let a := Vector.ofFn w
  fun i => a[i]

@[simp] theorem tabulateVec_eq (w : Fin d → K) : tabulateVec w = w := by
  funext i
  simp [tabulateVec]

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Cramer's rule with one denominator query and one determinant per output coordinate.
The guard keeps all divisions on the nonsingular branch. -/
def solveSquare (A : Matrix (Fin r) (Fin r) K) (b : Fin r → K) : Option (Fin r → K) :=
  let a := determinant A
  if a = 0 then none else
    some (tabulateVec fun i => determinant (A.updateCol i b) / a)

omit [IsStrictOrderedRing K] in
theorem solveSquare_formula (A : Matrix (Fin r) (Fin r) K) (b : Fin r → K) (h : A.det ≠ 0) :
    solveSquare A b = some (A.det⁻¹ • A.cramer b) := by
  simp only [solveSquare, determinant_eq, ite_eq_right h, tabulateVec_eq, Option.some.injEq]
  funext i
  simp [cramer_apply, div_eq_mul_inv, mul_comm]

omit [IsStrictOrderedRing K] in
theorem solveSquare_correct (A : Matrix (Fin r) (Fin r) K) (b x : Fin r → K)
    (h : solveSquare A b = some x) : A *ᵥ x = b := by
  by_cases hn : A.det = 0
  · simp [solveSquare, hn] at h
  · rw [solveSquare_formula A b hn, Option.some.injEq] at h
    rw [← h, Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hn, one_smul]

omit [IsStrictOrderedRing K] in
theorem solveSquare_mulVec (A : Matrix (Fin r) (Fin r) K) (c : Fin r → K) (h : A.det ≠ 0) :
    solveSquare A (A *ᵥ c) = some c := by
  have heq := solveSquare_formula A (A *ᵥ c) h
  have hsol := solveSquare_correct A _ _ heq
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h))
  rw [heq, hinj hsol]

/-- Send selected-column coefficients back to their original coordinates. -/
def scatter (s : List (Fin d)) (w : Fin s.length → K) : Fin d → K :=
  tabulateVec fun j => ∑ k, if s.get k = j then w k else 0

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem mulVec_scatter (A : Matrix (Fin m) (Fin d) K) (s : List (Fin d)) (w : Fin s.length → K) :
    A *ᵥ scatter s w = columns A s *ᵥ w := by
  ext i
  simp only [scatter, tabulateVec_eq, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp [mul_ite, columns]

/-- An exact solver. The final comparison rejects right-hand sides outside the column span. -/
def solve (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) : Option (Fin d → K) :=
  let s := columnBasis A
  let B := columns A s
  let G := tabulate (Bᵀ * B)
  let rhs := tabulateVec (Bᵀ *ᵥ b)
  match solveSquare G rhs with
  | none => none
  | some c =>
    let x := scatter s c
    if A *ᵥ x = b then some x else none

omit [IsStrictOrderedRing K] in
theorem solve_sound (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (z : Fin d → K)
    (h : solve A b = some z) : A *ᵥ z = b := by
  simp only [solve, tabulate_eq, tabulateVec_eq] at h
  split at h
  · contradiction
  · split at h <;> simp_all

theorem solve_complete (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K)
    (hx : ∃ x, A *ᵥ x = b) : ∃ x, solve A b = some x := by
  let s := columnBasis A
  let B := columns A s
  obtain ⟨hi, hs⟩ := columnBasis_spec A
  have hB : b ∈ LinearMap.range B.mulVecLin := by
    rw [Matrix.range_mulVecLin, show span K (Set.range B.col) = span K (Set.range A.col) from hs,
      ← Matrix.range_mulVecLin]
    exact hx
  obtain ⟨c, hBc⟩ := hB
  change B *ᵥ c = b at hBc
  have hdet : (Bᵀ * B).det ≠ 0 := by simpa using (gram_det_ne_zero B).2 hi
  have hG : solveSquare (Bᵀ * B) (Bᵀ *ᵥ b) = some c := by
    rw [← hBc, Matrix.mulVec_mulVec]
    exact solveSquare_mulVec _ _ hdet
  refine ⟨scatter s c, ?_⟩
  change (match solveSquare (tabulate (Bᵀ * B)) (tabulateVec (Bᵀ *ᵥ b)) with
    | none => none
    | some t => if A *ᵥ scatter s t = b then some (scatter s t) else none) = _
  simp only [tabulate_eq, tabulateVec_eq, hG, mulVec_scatter]
  exact ite_eq_left hBc

theorem solve_none_iff (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) :
    solve A b = none ↔ ¬ ∃ x, A *ᵥ x = b := by
  constructor
  · intro h hx
    obtain ⟨x, hx⟩ := solve_complete A b hx
    simp [h] at hx
  · intro h
    cases hs : solve A b with
    | none => rfl
    | some x => exact (h ⟨x, solve_sound A b x hs⟩).elim

end Elimination
end LinearProgramming
end Optimization
end OAI
