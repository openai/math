import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionDeformation
import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionJetRoots
import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Split-grid evaluation for the integral deformation

The two quadratic nodes and the scaled roots of the binomial provide one square Vandermonde
matrix each. Their tensor grid diagonalizes the long-jet product. Its inverse and the
linear readback at one recover all short-jet output coefficients.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial Matrix
open scoped Kronecker BigOperators

variable {R A σ : Type*} [CommRing R] [CommRing A] [Fintype σ] [DecidableEq σ]

/-- Coordinates of a basis monomial or evaluation point on the active axes. -/
abbrev Address (m : σ → ℕ) := ∀ i, Fin 2 × Fin (m i)

/-- Tensor of the two Vandermonde transforms on each active axis. -/
noncomputable def evaluationGrid (m : σ → ℕ) (u : σ → Fin 2 → A)
    (y : ∀ i, Fin (m i) → A) : Matrix (Address m) (Address m) A :=
  gridTensor fun i => vandermonde (u i) ⊗ₖ vandermonde (y i)

/-- The inverse tensor uses the inverse transforms on the two coordinates of every axis. -/
noncomputable def interpolationGrid (m : σ → ℕ) (u : σ → Fin 2 → A)
    (y : ∀ i, Fin (m i) → A) : Matrix (Address m) (Address m) A :=
  gridTensor fun i => (vandermonde (u i))⁻¹ ⊗ₖ (vandermonde (y i))⁻¹

private theorem unit_det_nodes {n : ℕ} (v : Fin n → A)
    (hv : Pairwise (fun i j => IsUnit (v i - v j))) : IsUnit (vandermonde v).det := by
  rw [det_vandermonde, IsUnit.prod_univ_iff]
  intro i
  exact IsUnit.prod_iff.mpr (fun _ hj => hv (Finset.mem_Ioi.mp hj).ne')

theorem interpolation_evaluation (m : σ → ℕ) (u : σ → Fin 2 → A) (y : ∀ i, Fin (m i) → A)
    (hu : ∀ i, Pairwise (fun j k => IsUnit (u i j - u i k)))
    (hy : ∀ i, Pairwise (fun j k => IsUnit (y i j - y i k))) :
    interpolationGrid m u y * evaluationGrid m u y = 1 := by
  unfold interpolationGrid evaluationGrid
  rw [← gridTensor_mul]
  simp only [← mul_kronecker_mul, nonsing_inv_mul _ (unit_det_nodes _ (hu _)),
    nonsing_inv_mul _ (unit_det_nodes _ (hy _)), one_kronecker_one, gridTensor_one]

theorem evaluationGrid_mul (φ : R[X] →+* A) (ρ β : σ → R) (m : σ → ℕ)
    (u : σ → Fin 2 → A) (y : ∀ i, Fin (m i) → A)
    (hu : ∀ i j, (u i j)^2 = -u i j - φ (C (ρ i)*X))
    (hy : ∀ i j, (y i j)^(m i) = φ (binomial (β i)))
    (x₁ x₂ : Address m → A) :
    (evaluationGrid m u y) *ᵥ multiply (fun a b c => φ (integralCoeff ρ β m a b c)) x₁ x₂ =
      ((evaluationGrid m u y) *ᵥ x₁) * ((evaluationGrid m u y) *ᵥ x₂) := by
  let E := evaluationGrid m u y
  have hE (s a b : Address m) :
      ∑ k, φ (integralCoeff ρ β m a b k) * E s k = E s a * E s b :=
    integral_normal_form φ ρ β m (fun i => u i (s i).1) (fun i => y i (s i).2)
      (fun i => hu _ _) (fun i => hy _ _) a b
  funext s
  change (∑ k, E s k * (∑ a, ∑ b, x₁ a * x₂ b * φ (integralCoeff ρ β m a b k))) =
    (∑ a, E s a * x₁ a) * ∑ b, E s b * x₂ b
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = ∑ k, (x₁ a * x₂ b) * (φ (integralCoeff ρ β m a b k) * E s k) := by
      apply Finset.sum_congr rfl
      intros
      ring
    _ = _ := by rw [← Finset.mul_sum, hE]; ring

/-- Multiply at the split points and apply the inverse tensor transform to recover the
product coefficients for any specialization admitting these nodes. -/
theorem interpolate_pointwise (φ : R[X] →+* A) (ρ β : σ → R) (m : σ → ℕ)
    (u : σ → Fin 2 → A) (y : ∀ i, Fin (m i) → A)
    (hu : ∀ i j, (u i j)^2 = -u i j - φ (C (ρ i)*X))
    (hy : ∀ i j, (y i j)^(m i) = φ (binomial (β i)))
    (hdu : ∀ i, Pairwise (fun j k => IsUnit (u i j - u i k)))
    (hdy : ∀ i, Pairwise (fun j k => IsUnit (y i j - y i k)))
    (x₁ x₂ : Address m → A) :
    interpolationGrid m u y *ᵥ ((evaluationGrid m u y *ᵥ x₁) * (evaluationGrid m u y *ᵥ x₂)) =
      multiply (fun a b k => φ (integralCoeff ρ β m a b k)) x₁ x₂ := by
  rw [← evaluationGrid_mul φ ρ β m u y hu hy, mulVec_mulVec,
    interpolation_evaluation m u y hdu hdy, one_mulVec]


private theorem atZero_X (h : ℕ) :
    specialize (0 : R) h X = AdjoinRoot.root (X ^ h) := by
  change aeval _ (taylor 0 X) = _
  rw [taylor_zero, aeval_X]

private theorem atZero_C (h : ℕ) (a : R) :
    specialize (0 : R) h (C a) = algebraMap R (Jet R h) a := by
  exact (specialize (0 : R) h).commutes a

omit [Fintype σ] [DecidableEq σ] in
/-- The node sets for evaluation are available in every long jet. The scalar hypotheses are
the invertibility of each width and the supplied roots of unity with pairwise unit differences. -/
theorem exists_split_nodes (h : ℕ) (ρ β : σ → R) (m : σ → ℕ)
    (hm : ∀ i, IsUnit (m i : R)) (v : ∀ i, Fin (m i) → R)
    (hv : ∀ i j, (v i j)^(m i) = 1)
    (hd : ∀ i, Pairwise (fun j k => IsUnit (v i j - v i k))) :
    ∃ (u : σ → Fin 2 → Jet R h) (y : ∀ i, Fin (m i) → Jet R h),
      (∀ i j, (u i j)^2 = -u i j - specialize 0 h (C (ρ i)*X)) ∧
      (∀ i j, (y i j)^(m i) = specialize 0 h (binomial (β i))) ∧
      (∀ i, Pairwise (fun j k => IsUnit (u i j - u i k))) ∧
      (∀ i, Pairwise (fun j k => IsUnit (y i j - y i k))) := by
  let z : Jet R h := AdjoinRoot.root (X ^ h)
  let g := algebraMap R (Jet R h)
  have hz := jetParameter_nilpotent R h
  choose a b ha hb ea eb hab using fun i => quadraticRootsAtZero z (g (ρ i)) hz
  choose w hw ew using fun i => binomialScalingAtZero z (g (β i)) hz (m i)
    (by simpa [g] using (hm i).map g)
  refine ⟨fun i => ![a i, b i], fun i j => (w i : Jet R h) * g (v i j), ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [map_mul, atZero_C, atZero_X]
    fin_cases j
    · change (a i)^2 = -a i - g (ρ i)*z
      linear_combination ea i
    · change (b i)^2 = -b i - g (ρ i)*z
      linear_combination eb i
  · intro i j
    rw [mul_pow, ← map_pow, hv, map_one, mul_one, ew, binomial]
    simp [g, z, atZero_C, atZero_X]
  · intro i j k hjk
    fin_cases j <;> fin_cases k <;> simp_all
    simpa using (hab i).neg
  · intro i j k hjk
    rw [← mul_sub, ← map_sub]
    exact (w i).isUnit.mul ((hd i hjk).map g)

/-- The integral block product uses identical input maps to the split grid, one pointwise
long-jet product per address, and a single common linear output map. -/
theorem split_integral_product (r : ℕ) (hr : 0 < r) (ρ β : σ → R) (m : σ → ℕ)
    (hm : ∀ i, IsUnit (m i : R)) (v : ∀ i, Fin (m i) → R)
    (hv : ∀ i j, (v i j)^(m i) = 1) (hd : ∀ i, Pairwise (fun j k => IsUnit (v i j - v i k))) :
    let H := 2*r + 2*Fintype.card σ
    ∃ (u : σ → Fin 2 → Jet R H) (y : ∀ i, Fin (m i) → Jet R H),
      let input := specialize (0 : R) H ∘ liftJet 1 r
      ∀ x₁ x₂ : Address m → Jet R r,
        readAtOne H r ∘ (interpolationGrid m u y *ᵥ
          ((evaluationGrid m u y *ᵥ (input ∘ x₁)) * (evaluationGrid m u y *ᵥ (input ∘ x₂)))) =
        multiply (fun a b k => specialize 1 r (integralCoeff ρ β m a b k)) x₁ x₂ := by
  dsimp only
  obtain ⟨u, y, hu, hy, hdu, hdy⟩ := exists_split_nodes (2*r+2*Fintype.card σ) ρ β m hm v hv hd
  refine ⟨u, y, fun x₁ x₂ => ?_⟩
  rw [interpolate_pointwise (specialize 0 _).toRingHom ρ β m u y hu hy hdu hdy]
  exact funext (recover_integral_multiply r hr ρ β m x₁ x₂)

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
