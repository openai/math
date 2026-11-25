import OAI.Optimization.LinearProgramming.Geometry.Oracle
import OAI.Optimization.LinearProgramming.Geometry.Projection
import OAI.Optimization.LinearProgramming.Geometry.Triangular

/-! Correctness of the actual rational test, from rounded primal and dual bases. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix
open scoped BigOperators Matrix

variable {r s n : ℕ}

/-- The clipping cutoff used for all minor requests of a system on `n` coordinates. -/
def geoCutoff (n : ℕ) : ℕ := 100 * (n + 1)^3

/-- The additive error budget on compressed magnitudes. -/
noncomputable def geoDelta (n : ℕ) : ℝ := (2 : ℝ) ^ (-(geoCutoff n : ℝ))

theorem geoDelta_nonneg (n : ℕ) : 0 ≤ geoDelta n := Real.rpow_nonneg (by norm_num) _

theorem abs_priceNormalize_le_one (t c : Fin n → ℝ) (i : Fin n) :
    |priceNormalize t c i| ≤ 1 := by
  let x := pricedVector t c
  change |x i / ‖x‖| ≤ 1
  rw [abs_div, abs_of_nonneg (norm_nonneg x)]
  by_cases hz : ‖x‖ = 0
  · simp [hz]
  · exact (div_le_one (lt_of_le_of_ne (norm_nonneg x) (Ne.symm hz))).mpr (norm_le_pi_norm x i)

private theorem squareLength_le_of_coordinateNorm {x : Fin n → ℝ}
    (hx : coordinateNorm x ≤ 1 / (2000 * n)) :
    squareLength x ≤ (labelTolerance n : ℝ)^2 / 4 := by
  have hτ : (1 : ℝ) / (2000 * n) = labelTolerance n / 2 := by
    unfold labelTolerance
    ring
  rw [hτ] at hx
  have h := pow_le_pow_left₀ (show 0 ≤ coordinateNorm x from norm_nonneg _) hx 2
  rw [coordinateNorm_sq] at h
  exact (show squareLength x ≤ (labelTolerance n / 2 : ℝ)^2 from h).trans (by linarith)

private theorem projection_independence {D : Matrix (Fin r) (Fin n) ℚ}
    (hD : LinearIndependent ℝ (D.map (Rat.castHom ℝ)).row) :
    IsUnit ((D.map (Rat.castHom ℝ)) * (D.map (Rat.castHom ℝ))ᵀ).det :=
  gram_det_isUnit_of_independent_rows _ hD

/-- Given the triangular coefficient estimate and the rounded row correlations,
run the entire designated label test using the *primal* rounded matrix alone.
The second matrix is used only for the proof, even when either rank is zero. -/
theorem label_from_rounded_row_bounds
    (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℝ)
    (hD : LinearIndependent ℝ (D.map (Rat.castHom ℝ)).row) (hE : LinearIndependent ℝ E.row)
    (hrank : r + s = n) (t : Fin n → ℝ) (C C' : Finset (Fin n → ℝ))
    (hC : ∀ c ∈ C, ∀ j, 0 ≤ c j) (hC' : ∀ c ∈ C', ∀ j, 0 ≤ c j)
    (hrows : ∀ i j, |(D.map (Rat.castHom ℝ)).row i ⬝ᵥ E.row j| ≤ 10*n*geoDelta n)
    (hcx : ∀ c ∈ C, ∀ j, |E.row j ⬝ᵥ priceNormalize t c| ≤ 10*n*geoDelta n)
    (hcy : ∀ c ∈ C', ∀ j,
        |(D.map (Rat.castHom ℝ)).row j ⬝ᵥ priceNormalize (-t) c| ≤ 10*n*geoDelta n)
    (hrepD : ∀ a : Fin r → ℝ, coordinateNorm ((D.map (Rat.castHom ℝ))ᵀ *ᵥ a) = 1 →
      ∑ j, |a j| ≤ 2^n)
    (hrepE : ∀ a : Fin s → ℝ, coordinateNorm (Eᵀ *ᵥ a) = 1 → ∑ j, |a j| ≤ 2^n)
    (i : Fin n) :
    let answer := fwLabel (1 - rowGramProjector D) i
    ((0 < circuitEnvelope C i ∧ ∀ j, 0 < circuitEnvelope C j →
       circuitCost C i + t i ≤ circuitCost C j + t j + 2) → answer = true) ∧
    ((0 < circuitEnvelope C' i ∧ ∀ j, 0 < circuitEnvelope C' j →
       circuitCost C' i - t i ≤ circuitCost C' j - t j + 2) → answer = false) := by
  let D' := D.map (Rat.castHom ℝ)
  have herr : 0 ≤ 10*(n:ℝ)*geoDelta n := by have := geoDelta_nonneg n; positivity
  have hbudget : 30 * (n : ℝ)^3 * 4^n * geoDelta n ≤ 1 / (2000 * n) :=
    projection_precision n i.pos
  have hbound := rounded_projector_estimates D' E hD hE hrank i.pos (geoDelta n)
    (geoDelta_nonneg _) hbudget
  apply rational_projectorLabel_spec hC hC' t (rowGramProjector D)
  · rw [rowGramProjector_map]
    exact rowGramProjector_transpose D'
  · rw [rowGramProjector_map]
    exact rowGramProjector_idempotent D' (projection_independence hD)
  · intro c hc
    rw [rowGramProjector_map]
    apply squareLength_le_of_coordinateNorm
    have h := (hbound (priceNormalize t c) 0 (abs_priceNormalize_le_one t c) hrows
      (fun j => by simpa only [dotProduct_zero, abs_zero] using herr) (hcx c hc) hrepD hrepE).1
    simpa only [sub_mulVec, one_mulVec] using h
  · intro c hc
    rw [rowGramProjector_map]
    apply squareLength_le_of_coordinateNorm
    exact (hbound 0 (priceNormalize (-t) c) (fun j => by simp) hrows (hcy c hc)
      (fun j => by simpa only [dotProduct_zero, abs_zero] using herr) hrepD hrepE).2

end Geometry
end LinearProgramming
end Optimization
end OAI
