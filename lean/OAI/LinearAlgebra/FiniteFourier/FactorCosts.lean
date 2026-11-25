import OAI.LinearAlgebra.FiniteFourier.ExtensionCostBound
import OAI.LinearAlgebra.FiniteFourier.GeometricCost
import OAI.LinearAlgebra.FiniteFourier.GridFactor

/-! # Uniform cost of a single geometric-grid axis -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open ExactFourier.CoefficientTime

universe u v

/-- A grid axis costs at most seven fixed convolutions of its side length,
uniformly over the field, the grid ratio and the Toeplitz coefficients. -/
theorem gridFactor_cost_of_convolution {K : Type*} [Field K] {β C : ℝ}
    (hC : 0 ≤ C) (hconv : FixedConvolutionBound K β C) {a : ℕ} (ha : 0 < a)
    {T : Matrix (Fin a) (Fin a) K} (hT : GridFactor T) :
    (complexity T : ℝ) ≤ (7 * C) * a * (1 + Real.logb 2 a) ^ β := by
  let B := convolutionBudget β C a
  have hB (f : PowerSeries K) (_ : f.constantCoeff ≠ 0) : RealizableAtMost (truncMatrix a f) B :=
    hconv.realizable _ _
  have hcost : complexity T ≤ 7 * B := by
    cases hT with
    | geometric q hq hd => exact geometric_cost_of_convolution q hq hd hB _ (Or.inl rfl)
    | inverseGeometric q hq hd => exact geometric_cost_of_convolution q hq hd hB _ (Or.inr rfl)
    | lower f hf =>
      exact ((complexity_le_iff ..).2 (hB f hf)).trans (by omega)
    | upper f hf =>
      exact ((complexity_le_iff ..).2 ((IsGridDiagonalOrToeplitz.upper f hf).realizable hB)).trans
        (by omega)
  have hreal : (complexity T : ℝ) ≤ 7 * B := by exact_mod_cast hcost
  exact hreal.trans <| calc
    7 * (B : ℝ) ≤ 7 * (C * a * (1 + Real.logb 2 a) ^ β) :=
      mul_le_mul_of_nonneg_left (convolutionBudget_le hC ha) (by norm_num)
    _ = _ := by ring

/-- The companion's uniform fixed-convolution estimate provides one constant
for every allowed grid axis over every ground field, at the same exponent. -/
theorem UniformGridInputs.gridFactor_cost (h : UniformGridInputs.{u}) (β : ℝ)
    (hβ : 1 / 2 < β) (hβ' : β < 1) :
    ∃ C > (0 : ℝ), ∀ (K : Type u) [Field K], ∀ {a : ℕ}, 2 ≤ a →
      ∀ (T : Matrix (Fin a) (Fin a) K), GridFactor T →
        (complexity T : ℝ) ≤ C * a * (1 + Real.logb 2 a) ^ β := by
  obtain ⟨C, hC, hK⟩ := h β hβ hβ'
  refine ⟨7 * C, by positivity, fun K _ a ha T hT ↦ ?_⟩
  exact gridFactor_cost_of_convolution hC.le (hK K).1 (by omega) hT

/-- The scalar-restriction constant is uniform in the ground field, extension,
power basis and prescribed multiplier. -/
theorem UniformGridInputs.powerBasis_scalar_cost (h : UniformGridInputs.{u}) (β : ℝ)
    (hβ : 1 / 2 < β) (hβ' : β < 1) :
    ∃ C > (0 : ℝ), ∀ (K : Type u) (E : Type v) [Field K] [Field E] [Algebra K E],
      ∀ (pb : PowerBasis K E) (u : E),
        (complexity (fun i j ↦ pb.basis.repr (u * pb.basis j) i) : ℝ) ≤
          C * pb.dim * (1 + Real.logb 2 pb.dim) ^ β := by
  obtain ⟨C, hC, hK⟩ := h β hβ hβ'
  refine ⟨6 * C + 1, by positivity, fun K E _ _ _ pb u ↦ ?_⟩
  exact (hK K).1.powerBasis_scalar (by linarith) hβ'.le hC.le pb u

/-- Acting on every complementary fiber multiplies the one-axis circuit cost by
the number of fibers. The resulting estimate uses the total grid volume. -/
theorem axis_fiber_cost_of_convolution {K : Type*} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {a : ι → ℕ} (A : ∀ j, Matrix (Fin (a j)) (Fin (a j)) K)
    {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C) (hconv : FixedConvolutionBound K β C)
    (ha : ∀ j, 0 < a j) (i : ι) (hT : GridFactor (A i)) :
    ((Fintype.card (∀ j : {j // j ≠ i}, Fin (a j.val)) * complexity (A i) : ℕ) : ℝ) ≤
      (7 * C) * ((∏ j, a j : ℕ) : ℝ) * (1 + Real.logb 2 (∏ j, a j : ℕ)) ^ β := by
  classical
  let F := (∀ j : {j // j ≠ i}, Fin (a j.val))
  let N := ∏ j, a j
  let f := Fintype.card F
  have he : a i * f = N := by
    have hh := (Fintype.card_congr (Equiv.piSplitAt i (fun j ↦ Fin (a j)))).symm
    rw [Fintype.card_prod, Fintype.card_fin] at hh
    exact hh.trans (by simp [N, Fintype.card_pi])
  have : Nonempty F := ⟨fun j ↦ ⟨0, ha _⟩⟩
  have hf : 0 < f := Fintype.card_pos
  have hai : a i ≤ N := he ▸ Nat.le_mul_of_pos_right _ hf
  have hone : (1 : ℝ) ≤ a i := by exact_mod_cast ha i
  have hlog := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hone
  have hle := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (show (0 : ℝ) < a i by exact_mod_cast ha i) (show (a i : ℝ) ≤ N by exact_mod_cast hai)
  have hh : (1 + Real.logb 2 (a i)) ^ β ≤ (1 + Real.logb 2 N) ^ β :=
    Real.rpow_le_rpow (by linarith) (by linarith) hβ
  have he' : (a i : ℝ) * f = N := by exact_mod_cast he
  rw [Nat.cast_mul]
  calc
    (f : ℝ) * (complexity (A i) : ℝ) ≤ f * ((7 * C) * a i * (1 + Real.logb 2 (a i)) ^ β) :=
      mul_le_mul_of_nonneg_left (gridFactor_cost_of_convolution hC hconv (ha i) hT) (by positivity)
    _ = (7 * C) * ((a i : ℝ) * f) * (1 + Real.logb 2 (a i)) ^ β := by ring
    _ ≤ (7 * C) * (N : ℝ) * (1 + Real.logb 2 N) ^ β := by
      rw [he']
      exact mul_le_mul_of_nonneg_left hh (by positivity)

end FiniteFourier
end LinearAlgebra
end OAI
