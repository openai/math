import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-! # Passing from an echelon matrix to its diagonal blocks

Scale row block `i` by `z⁻ⁱ` and column block `j` by `zʲ`.
For a block upper triangular matrix the entries extend polynomially to zero.
Thus every polynomial test that vanishes on the scaled matrices also vanishes
on the direct sum of their diagonal blocks.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier
open scoped Polynomial
variable {K I O : Type*} [Field K]

theorem block_diagonal_specialization [Infinite K] (A : Matrix O I K)
    (rowBlock : O → ℕ) (colBlock : I → ℕ)
    (htri : ∀ i j, colBlock j < rowBlock i → A i j = 0)
    (p : MvPolynomial (O × I) K)
    (h : ∀ z : K, z ≠ 0 → MvPolynomial.eval
      (fun ij => (z ^ rowBlock ij.1)⁻¹ * A ij.1 ij.2 * z ^ colBlock ij.2) p = 0) :
    MvPolynomial.eval (fun ij => if rowBlock ij.1 = colBlock ij.2 then A ij.1 ij.2 else 0) p = 0 := by
  let entry (ij : O × I) : K[X] :=
    Polynomial.C (A ij.1 ij.2) * Polynomial.X ^ (colBlock ij.2 - rowBlock ij.1)
  let P := MvPolynomial.eval₂Hom Polynomial.C entry p
  have evalP (z : K) : P.eval z =
      MvPolynomial.eval (fun ij => A ij.1 ij.2 * z ^ (colBlock ij.2 - rowBlock ij.1)) p := by
    change Polynomial.evalRingHom z (MvPolynomial.eval₂Hom Polynomial.C entry p) = _
    rw [MvPolynomial.map_eval₂Hom]
    congr 1
    ext j <;> simp [entry]
  have onUnits (z : K) (hz : z ≠ 0) : P.eval z = 0 := by
    rw [evalP, ← h z hz]
    apply congrArg (fun v : O × I → K => MvPolynomial.eval v p)
    funext ⟨i,j⟩
    by_cases le : rowBlock i ≤ colBlock j
    · have he : z ^ colBlock j = z ^ (colBlock j - rowBlock i) * z ^ rowBlock i := by
        rw [← pow_add, Nat.sub_add_cancel le]
      rw [he]
      field_simp
    · simp [htri i j (lt_of_not_ge le)]
  have zero : P = 0 := by
    apply P.eq_zero_of_infinite_isRoot
    exact ((Set.finite_singleton (0 : K)).infinite_compl).mono (fun z hz => onUnits z hz)
  have atZero := evalP 0
  have spec : (fun ij : O × I => A ij.1 ij.2 * (0 : K) ^ (colBlock ij.2 - rowBlock ij.1)) =
      (fun ij => if rowBlock ij.1 = colBlock ij.2 then A ij.1 ij.2 else 0) := by
    funext ⟨i,j⟩
    rcases lt_trichotomy (rowBlock i) (colBlock j) with hlt | he | hgt
    · simp [hlt.ne, zero_pow (Nat.sub_pos_of_lt hlt).ne']
    · simp [he]
    · simp [htri i j hgt]
  rw [spec, zero, Polynomial.eval_zero] at atZero
  exact atZero.symm

end FiniteFourier
end LinearAlgebra
end OAI
