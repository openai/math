import OAI.LinearAlgebra.FiniteFourier.PrimeKernel
import OAI.LinearAlgebra.FiniteFourier.GridInputs

/-! # The binary Fourier word for the unit shear

The companion paper produces a unit shear from four two-coordinate Fourier
transforms and diagonal scalings. Tensoring the entire factorization keeps
the number of transform calls equal to four.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Matrix
variable {K : Type*} [Field K]

private def circ (z : K) : Matrix (Fin 2) (Fin 2) K := !![1,z; z,1]

private theorem circ_eq_fourier (z : K) (h2 : (2 : K) ≠ 0) :
    circ z = dftMatrix 2 (-1 : K) * diagonal ![(1+z)/2, (1-z)/2] * dftMatrix 2 (-1 : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [circ, dftMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply] <;> field_simp <;> ring

private theorem shear_from_circ {x : K} (hx : x ≠ 0) (h₄ : x^4 ≠ 1) :
    unitShear K = diagonal ![(1-x^2)⁻¹, -x/(x^4-1)] * circ x *
      diagonal ![1, -1/x] * circ (x^2) * diagonal ![1, -1] := by
  have h₁ : 1 - x^2 ≠ 0 := by
    intro h
    apply h₄
    calc
      x^4 = (x^2)^2 := by ring
      _ = 1 := by rw [show x^2 = 1 by linear_combination -h]; norm_num
  have h₄' : x^4-1 ≠ 0 := sub_ne_zero.mpr h₄
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [unitShear, circ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] <;>
    field_simp <;> ring

private theorem gridTensor_diagonal_free (j : ℕ) (v : Fin 2 → K) :
    RealizableAtMost (gridTensor (fun _ : Fin j => diagonal v)) 0 := by
  let v' (i : Fin j → Fin 2) := ∏ u, v (i u)
  let p : Circuit K (Fin j → Fin 2) (Fin j → Fin 2) 0 :=
    ⟨.nil, fun i => .scaled (v' i) (.inl i)⟩
  refine ⟨0, le_rfl, p, ?_⟩
  ext i k
  by_cases h : i = k
  · subst k
    simp [p, v', Circuit.matrix, Circuit.eval, Readout.eval, gridTensor]
  · have hdiff : ∃ u, i u ≠ k u := by
      exact not_forall.mp (fun he => h (funext he))
    obtain ⟨u, hu⟩ := hdiff
    have hz : ∏ a, diagonal v (i a) (k a) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ u) (diagonal_apply_ne _ hu)
    simpa [p, Circuit.matrix, Circuit.eval, Readout.eval, gridTensor, Pi.single_apply, h]
      using hz.symm

/-- The shear on `j` bits costs at most four positive-sign binary Fourier
tensor calls whenever the diagonal scalars of the companion word exist in K. -/
theorem complexity_shear_le_four_binary {x : K} (h2 : (2 : K) ≠ 0)
    (hx : x ≠ 0) (h₄ : x ^ 4 ≠ 1) (j : ℕ) :
    complexity (gridTensor (fun _ : Fin j => unitShear K)) ≤
      4 * complexity (primeTransform 2 j (-1 : K)) := by
  let H := dftMatrix 2 (-1 : K)
  let s := complexity (primeTransform 2 j (-1 : K))
  have hh : RealizableAtMost (gridTensor (fun _ : Fin j => H)) s :=
    realizableAtMost_complexity (primeTransform 2 j (-1 : K))
  have hc (z : K) : RealizableAtMost (gridTensor (fun _ : Fin j => circ z)) (s+s) := by
    simp_rw [circ_eq_fourier z h2]
    rw [gridTensor_mul, gridTensor_mul]
    simpa using ((hh.mul (gridTensor_diagonal_free j ![(1+z)/2, (1-z)/2])).mul hh)
  apply (complexity_le_iff ..).mpr
  simp_rw [shear_from_circ hx h₄]
  rw [gridTensor_mul, gridTensor_mul, gridTensor_mul, gridTensor_mul]
  have h := ((((gridTensor_diagonal_free j ![(1-x^2)⁻¹, -x/(x^4-1)]).mul (hc x)).mul
    (gridTensor_diagonal_free j ![1, -1/x])).mul (hc (x^2))).mul (gridTensor_diagonal_free j ![1,-1])
  convert h using 1
  dsimp [s]
  omega

/-- A strict finite-template saving for the binary Fourier kernel implies
the companion shear bound needed by the geometric grid proof. -/
theorem shearTensorBound_of_binary_batch {x : K} (h2 : (2 : K) ≠ 0)
    (hx : x ≠ 0) (h₄ : x ^ 4 ≠ 1) {A W σ C : ℕ} {θ : ℝ}
    (hA : 0 < A) (hW : 0 < W) (hθ : 0 ≤ θ)
    (hs : (σ : ℝ) / W < (A : ℝ)^θ) (hb : PrimeKernelBatch 2 A W σ C (-1 : K)) :
    ∃ D > (0 : ℝ), ShearTensorBound K θ D := by
  obtain ⟨c, hc, hcost⟩ := primeTransform_bound_of_batch (by decide) hA hW hθ hs hb
  refine ⟨4*c, by positivity, fun j => ?_⟩
  have hj := complexity_shear_le_four_binary h2 hx h₄ j
  have hj' : (complexity (gridTensor (fun _ : Fin j => unitShear K)) : ℝ) ≤
      4 * (complexity (primeTransform 2 j (-1 : K)) : ℝ) := by exact_mod_cast hj
  have cut := mul_le_mul_of_nonneg_left (hcost j) (by norm_num : (0 : ℝ) ≤ 4)
  push_cast at cut
  linarith

end

end

end FiniteFourier
end LinearAlgebra
end OAI
