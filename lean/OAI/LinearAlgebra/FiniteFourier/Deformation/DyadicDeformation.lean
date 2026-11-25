import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionDeformationSplit

/-! # Common-parameter deformation of binomial blocks

The dyadic denominator-avoidance branch has one binomial per active axis.
A product of two basis monomials can wrap at most once on each axis.
Consequently a jet of length `2*r + card σ` recovers the product at one.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation.Dyadic

open Polynomial Matrix
open scoped BigOperators

variable {R A σ : Type*} [CommRing R] [CommRing A]

/-- An exponent tuple in the power basis for the active binomials. -/
abbrev Address (m : σ → ℕ) := ∀ i, Fin (m i)

/-- The coefficient of a basis monomial in a product on one binomial axis. -/
def axisCoeff (β : R) {m : ℕ} (a b k : Fin m) : R :=
  if k.val = (a.val + b.val) % m then (if a.val + b.val < m then 1 else β) else 0

theorem map_axisCoeff (φ : R →+* A) (β : R) {m : ℕ} (a b k : Fin m) :
    φ (axisCoeff β a b k) = axisCoeff (φ β) a b k := by
  simp only [axisCoeff, apply_ite φ, map_zero, map_one]

/-- A general binomial quotient specializes the deformed one. -/
theorem axisCoeff_normal_form (β y : R) {m : ℕ} (hy : y ^ m = β) (a b : Fin m) :
    ∑ k, axisCoeff β a b k * y ^ k.val = y ^ a.val * y ^ b.val := by
  let φ := evalRingHom (1 : R)
  have he : φ (binomial β) = β := by simp [φ, binomial]
  have h := binomial_normal_form φ β y (hy.trans he.symm) a b
  simpa only [binomialCoeff, apply_ite φ, map_one, map_zero, he, axisCoeff] using h

/-- Structure constants of a product of binomial algebras in its monomial basis. -/
def coeff [Fintype σ] (β : σ → R) (m : σ → ℕ) (a b k : Address m) : R :=
  ∏ i, axisCoeff (β i) (a i) (b i) (k i)

theorem map_coeff [Fintype σ] (φ : R →+* A) (β : σ → R) (m : σ → ℕ) (a b k : Address m) :
    φ (coeff β m a b k) = coeff (φ ∘ β) m a b k := by
  simp only [coeff, map_prod, map_axisCoeff, Function.comp_apply]

/-- One affine factor per wrap bounds the degree of the common-parameter structure constants. -/
theorem natDegree_coeff [Fintype σ] (β : σ → R) (m : σ → ℕ) (a b k : Address m) :
    (coeff (binomial ∘ β) m a b k).natDegree ≤ Fintype.card σ := by
  refine (natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ _i : σ, 1 := Finset.sum_le_sum fun i _ => natDegree_binomialCoeff (β i) ..
    _ = _ := by simp

variable [Fintype σ] [DecidableEq σ]

/-- Read the product at one after a single common lift, multiplication at zero, and recovery. -/
theorem recover (r : ℕ) (hr : 0 < r) (β : σ → R) (m : σ → ℕ) (x y : Address m → Jet R r) :
    let H := 2*r + Fintype.card σ
    let input := specialize (0 : R) H ∘ liftJet 1 r
    readAtOne H r ∘ multiply (coeff (fun i => specialize 0 H (binomial (β i))) m)
        (input ∘ x) (input ∘ y) =
      multiply (coeff (fun i => specialize 1 r (binomial (β i))) m) x y := by
  dsimp only
  funext k
  have hmap (t : R) (n : ℕ) (a b k : Address m) :
      specialize t n (coeff (binomial ∘ β) m a b k) =
        coeff (fun i => specialize t n (binomial (β i))) m a b k :=
    map_coeff (specialize t n).toRingHom ..
  simpa only [hmap, Function.comp_apply] using
    recover_multiply r (Fintype.card σ) hr (coeff (binomial ∘ β) m) (natDegree_coeff β m) x y k

/-- Tensor of the single-axis evaluation matrices. -/
noncomputable def evaluation (m : σ → ℕ) (v : ∀ i, Fin (m i) → R) :
    Matrix (Address m) (Address m) R := gridTensor fun i => vandermonde (v i)

/-- Tensor of the single-axis interpolation matrices. -/
noncomputable def interpolation (m : σ → ℕ) (v : ∀ i, Fin (m i) → R) :
    Matrix (Address m) (Address m) R := gridTensor fun i => (vandermonde (v i))⁻¹

theorem interpolation_evaluation (m : σ → ℕ) (v : ∀ i, Fin (m i) → R)
    (hd : ∀ i, Pairwise fun j k => IsUnit (v i j - v i k)) :
    interpolation m v * evaluation m v = 1 := by
  have hdet i : IsUnit (vandermonde (v i)).det := by
    rw [det_vandermonde, IsUnit.prod_univ_iff]
    intro j
    exact IsUnit.prod_iff.mpr fun _ hk => hd i (Finset.mem_Ioi.mp hk).ne'
  simp only [interpolation, evaluation, ← gridTensor_mul, nonsing_inv_mul _ (hdet _),
    gridTensor_one]

/-- Evaluation sends a product in the binomial block to pointwise multiplication. -/
theorem evaluation_multiply (β : σ → R) (m : σ → ℕ) (v : ∀ i, Fin (m i) → R)
    (hv : ∀ i j, v i j ^ m i = β i) (x y : Address m → R) :
    evaluation m v *ᵥ multiply (coeff β m) x y =
      (evaluation m v *ᵥ x) * (evaluation m v *ᵥ y) := by
  let E := evaluation m v
  have hE (s a b : Address m) : ∑ k, coeff β m a b k * E s k = E s a * E s b := by
    simp only [coeff, E, evaluation, gridTensor, vandermonde_apply, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun i k => axisCoeff (β i) (a i) (b i) k * v i (s i) ^ k.val)]
    exact Finset.prod_congr rfl fun i _ => axisCoeff_normal_form _ _ (hv i _) _ _
  funext s
  change (∑ k, E s k * (∑ a, ∑ b, x a * y b * coeff β m a b k)) =
    (∑ a, E s a * x a) * ∑ b, E s b * y b
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = ∑ k, (x a * y b) * (coeff β m a b k * E s k) := by
      apply Finset.sum_congr rfl
      intros
      ring
    _ = _ := by rw [← Finset.mul_sum, hE]; ring

/-- A split binomial block multiplies using two transforms, pointwise multiplication,
and one inverse transform. -/
theorem interpolate_pointwise (β : σ → R) (m : σ → ℕ) (v : ∀ i, Fin (m i) → R)
    (hv : ∀ i j, v i j ^ m i = β i) (hd : ∀ i, Pairwise fun j k => IsUnit (v i j - v i k))
    (x y : Address m → R) :
    interpolation m v *ᵥ ((evaluation m v *ᵥ x) * (evaluation m v *ᵥ y)) =
      multiply (coeff β m) x y := by
  rw [← evaluation_multiply β m v hv, mulVec_mulVec, interpolation_evaluation m v hd, one_mulVec]

end Deformation.Dyadic

end FiniteFourier
end LinearAlgebra
end OAI
