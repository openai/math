import OAI.LinearAlgebra.FiniteFourier.Bounds
import OAI.LinearAlgebra.FiniteFourier.InverseBorder

/-! # Uniform Fourier complexity, its inverse and the logarithmic exponent

The two inputs to the assembly theorem are the uniform forward estimates.
Free scaled readouts, self-duality and geometric-border invariance provide
the identical bounds with the same constants in the inverse direction.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
universe u v
open Filter
open scoped Topology

/-- Theorem 1.1, including the geometric-border feedback systems in each
direction. Every order and every group and admissible field use the same
lower constant, and the upper constant depends only on the positive slack. -/
def FourierComplexityTheorem : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (G : Type u) (K : Type v) [AddCommGroup G] [Fintype G] [Field K],
      Admissible G K → 2 ≤ Fintype.card G →
      let N : ℝ := Fintype.card G
      let lower := c * N * Real.sqrt (Real.logb (2 : ℕ) N)
      let upper := C * N * (1 + Real.logb (2 : ℕ) N) ^ ((1 : ℝ) / (2 : ℕ) + ε)
      (lower ≤ complexity (fourierMatrix G K) ∧ (complexity (fourierMatrix G K) : ℝ) ≤ upper) ∧
      (lower ≤ complexity (inverseFourierMatrix G K) ∧
        (complexity (inverseFourierMatrix G K) : ℝ) ≤ upper) ∧
      ∀ S : ℕ, (GeometricBorderAtMost (fourierMatrix G K) S ∨
        GeometricBorderAtMost (inverseFourierMatrix G K) S) → lower ≤ S

theorem fourierComplexityTheorem_of_estimates
    (hlo : UniformFourierBorderLower.{u,v}) (hhi : UniformFourierUpper.{u,v}) :
    FourierComplexityTheorem.{u,v} := by
  obtain ⟨c, hc, h⟩ := hlo
  refine ⟨c, hc, fun ε hε => ?_⟩
  obtain ⟨C, hC, hh⟩ := hhi ε hε
  refine ⟨C, hC, ?_⟩
  intro G K _ _ _ had hN
  have he := h G K had hN _ (realizableAtMost_complexity _).geometricBorder
  have hi := hh G K had hN
  dsimp only
  rw [complexity_inverseFourierMatrix G K had]
  refine ⟨⟨he,hi⟩, ⟨he,hi⟩, fun S hS => h _ _ had hN S ?_⟩
  exact hS.elim id (geometricBorderAtMost_inverseFourierMatrix_iff G K had S).mp

/-- The equality with a vanishing exponent error is a literal formulation
of `N (log N)^(1/2 + o(1))`. -/
theorem FiniteCostBounds.exists_vanishing_exponent_error {ι : Type*} {size cost : ι → ℕ}
    (B : FiniteCostBounds size cost) {l : Filter ι} (hN : Tendsto size l atTop) :
    ∃ η : ι → ℝ, Tendsto η l (𝓝 0) ∧ ∀ᶠ i in l,
      (cost i : ℝ) = (size i : ℝ) * (Real.logb 2 (size i)) ^ ((1 : ℝ)/2 + η i) := by
  let η (i : ι) := logOverhead (size i) (cost i) - 1/2
  refine ⟨η, ?_, ?_⟩
  · simpa [η] using (B.tendsto_logOverhead hN).sub_const ((1 : ℝ)/2)
  obtain ⟨c, hc, hlow⟩ := B.lower
  filter_upwards [hN.eventually_ge_atTop 4] with i hi
  have hn : 2 < (size i : ℝ) := by exact_mod_cast (show 2 < size i by omega)
  have hn' : 0 < (size i : ℝ) := by linarith
  have hx : 1 < Real.logb 2 (size i) := by
    calc
      1 = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ < _ := Real.logb_lt_logb (by norm_num) (by norm_num) hn
  have hc' : 0 < (cost i : ℝ) :=
    (mul_pos (mul_pos hc hn') (Real.sqrt_pos.mpr (by linarith))).trans_le (hlow i (by omega))
  have he : (1 : ℝ)/2 + η i = Real.logb (Real.logb 2 (size i)) (cost i / (size i : ℝ)) := by
    dsimp [η,logOverhead]
    rw [add_comm, sub_add_cancel]
    simp only [Real.logb]
    field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0:ℝ)<2) (by norm_num),
      (Real.log_pos hx).ne']
  rw [he, Real.rpow_logb (by linarith) hx.ne' (div_pos hc' hn'), mul_comm, div_mul_cancel₀ _ hn'.ne']

/-- The same finite estimates apply pointwise along a family whose groups
and coefficient fields both vary. -/
theorem FourierComplexityTheorem.finiteCostBounds (h : FourierComplexityTheorem.{u,v})
    {ι : Type*} (G : ι → Type u) (K : ι → Type v)
    [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)] [∀ i, Field (K i)]
    (had : ∀ i, Admissible (G i) (K i)) :
    FiniteCostBounds (fun i => Fintype.card (G i))
      (fun i => complexity (fourierMatrix (G i) (K i))) := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨⟨c, hc, ?_⟩, ?_⟩
  · obtain ⟨_, _, h₁⟩ := h 1 zero_lt_one
    exact fun i hi => (h₁ _ _ (had i) hi).1.1
  · intro ε hε
    obtain ⟨C, hC, hε'⟩ := h ε hε
    exact ⟨C, hC, fun i hi => (hε' _ _ (had i) hi).1.2⟩

/-- The explicit vanishing error applies to both directions along every
family of increasing orders in admissible fields. -/
theorem FourierComplexityTheorem.vanishing_exponent (h : FourierComplexityTheorem.{u,v})
    {ι : Type*} (G : ι → Type u) (K : ι → Type v)
    [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)] [∀ i, Field (K i)]
    (had : ∀ i, Admissible (G i) (K i)) {l : Filter ι}
    (hN : Tendsto (fun i => Fintype.card (G i)) l atTop) :
    ∃ η : ι → ℝ, Tendsto η l (𝓝 0) ∧ ∀ᶠ i in l,
      let N : ℝ := Fintype.card (G i)
      let size := N * (Real.logb 2 N) ^ ((1 : ℝ)/2 + η i)
      (complexity (fourierMatrix (G i) (K i)) : ℝ) = size ∧
        (complexity (inverseFourierMatrix (G i) (K i)) : ℝ) = size := by
  obtain ⟨η, hη, he⟩ := (h.finiteCostBounds G K had).exists_vanishing_exponent_error hN
  refine ⟨η, hη, ?_⟩
  filter_upwards [he] with i hi
  exact ⟨hi, by simpa only [complexity_inverseFourierMatrix _ _ (had i)] using hi⟩

end

end FiniteFourier
end LinearAlgebra
end OAI
