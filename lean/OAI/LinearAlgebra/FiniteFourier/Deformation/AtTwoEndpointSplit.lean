import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionDeformationSplit
import OAI.LinearAlgebra.FiniteFourier.Cyclic

/-! # Fourier factors of the split endpoint

In the long jet the binomial nodes are a common unit multiple of the powers of a
Fourier root. Thus one diagonal scaling per monomial converts the entire evaluation
grid to a tensor of binary Vandermondes and Fourier matrices. Interpolation uses the
reciprocal scales, the inverse binary Vandermondes, and normalized inverse-root DFTs.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Matrix Polynomial
open scoped BigOperators Kronecker

variable {A R σ : Type*} [CommRing A] [CommRing R] {m : ℕ}

/-- The Fourier nodes of a binomial after multiplying its roots by their common scale. -/
def scaledNodes (m : ℕ) (w ζ : Aˣ) (j : Fin m) : A := (w : A) * (ζ : A)^j.val

/-- Scaling the monomial of degree `j` by `w^j` precedes the unscaled Fourier transform. -/
theorem vandermonde_scaledNodes (w ζ : Aˣ) :
    vandermonde (scaledNodes m w ζ) =
      dftMatrix m (ζ : A) * diagonal (fun j : Fin m => (w : A)^j.val) := by
  ext i j
  simp [vandermonde_apply, scaledNodes, Matrix.mul_diagonal, dftMatrix, mul_pow, pow_mul, mul_comm]

/-- Orthogonality over a ring follows from the unit differences of Fourier nodes. -/
theorem normalized_dftMatrix_mul_of_unit_differences (ζ : Aˣ) (hζ : ζ^m = 1)
    (hm : IsUnit (m : A))
    (hd : Pairwise (fun i j : Fin m => IsUnit ((ζ:A)^i.val - (ζ:A)^j.val))) :
    (((hm.unit⁻¹ : Aˣ) : A) • dftMatrix m ((ζ⁻¹ : Aˣ) : A)) * dftMatrix m (ζ : A) = 1 := by
  rw [Matrix.smul_mul]
  ext i j
  let q : Aˣ := (ζ^i.val)⁻¹ * ζ^j.val
  have hentry : (dftMatrix m (↑ζ⁻¹ : A) * dftMatrix m (ζ : A)) i j =
      ∑ k : Fin m, (q : A)^k.val := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    simp [dftMatrix, q, mul_pow, ← inv_pow, ← pow_mul, Nat.mul_comm]
  rw [Matrix.smul_apply, hentry, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp [q]
  · simp only [hij, ↓reduceIte]
    have hdiff : IsUnit ((q : A) - 1) := by
      convert ((ζ^i.val)⁻¹).isUnit.mul (hd (Ne.symm hij)) using 1
      change (↑((ζ^i.val)⁻¹) : A) * (ζ:A)^j.val - 1 =
        ↑((ζ^i.val)⁻¹) * ((ζ:A)^j.val - (ζ:A)^i.val)
      rw [mul_sub]
      rw [← Units.val_pow_eq_pow_val ζ i.val, Units.inv_mul]
    have hqm : q^m = 1 := by
      simp only [q, mul_pow, inv_pow]
      rw [← pow_mul, Nat.mul_comm i.val, pow_mul, hζ, one_pow, inv_one, one_mul,
        ← pow_mul, Nat.mul_comm j.val, pow_mul, hζ, one_pow]
    have hz : ∑ k ∈ Finset.range m, (q : A)^k = 0 := by
      apply hdiff.mul_right_cancel
      rw [geom_sum_mul, ← Units.val_pow_eq_pow_val, hqm]
      simp
    rw [Fin.sum_univ_eq_sum_range, hz, smul_zero]

/-- The inverse exists with the expected normalization over the coefficient ring. -/
theorem inv_dftMatrix_of_unit_differences (ζ : Aˣ) (hζ : ζ^m = 1)
    (hm : IsUnit (m : A))
    (hd : Pairwise (fun i j : Fin m => IsUnit ((ζ:A)^i.val - (ζ:A)^j.val))) :
    (dftMatrix m (ζ : A))⁻¹ =
      ((hm.unit⁻¹ : Aˣ) : A) • dftMatrix m ((ζ⁻¹ : Aˣ) : A) := by
  exact Matrix.inv_eq_left_inv (normalized_dftMatrix_mul_of_unit_differences ζ hζ hm hd)

variable [Fintype σ] [DecidableEq σ]

/-- The product of the monomial scaling factors, a unit for every address. -/
def splitAddressScale (m : σ → ℕ) (w : σ → Aˣ) (a : Address m) : Aˣ :=
  ∏ i, w i ^ (a i).2.val

/-- Evaluation uses one unit diagonal on the tuple of monomial exponents. -/
theorem evaluationGrid_fourier (m : σ → ℕ) (u : σ → Fin 2 → A) (w ζ : σ → Aˣ) :
    evaluationGrid m u (fun i => scaledNodes (m i) (w i) (ζ i)) =
      gridTensor (fun i => vandermonde (u i) ⊗ₖ dftMatrix (m i) (ζ i : A)) *
        diagonal (fun a => (splitAddressScale m w a : A)) := by
  ext a b
  rw [Matrix.mul_diagonal]
  simp only [evaluationGrid, gridTensor, kroneckerMap_apply, splitAddressScale, Units.coe_prod,
    Units.val_pow_eq_pow_val, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp [vandermonde_apply, scaledNodes, dftMatrix, mul_pow, pow_mul]
  ring

/-- Interpolation applies normalized inverse-root DFTs, then the reciprocal unit diagonal. -/
theorem interpolationGrid_fourier (m : σ → ℕ) (u : σ → Fin 2 → A) (w ζ : σ → Aˣ)
    (hm : ∀ i, IsUnit (m i : A)) (hζ : ∀ i, (ζ i)^(m i) = 1)
    (hd : ∀ i, Pairwise (fun j k : Fin (m i) => IsUnit ((ζ i : A)^j.val - (ζ i : A)^k.val))) :
    interpolationGrid m u (fun i => scaledNodes (m i) (w i) (ζ i)) =
      diagonal (fun a => (↑(splitAddressScale m w a)⁻¹ : A)) *
        gridTensor (fun i => (vandermonde (u i))⁻¹ ⊗ₖ
          ((((hm i).unit⁻¹ : Aˣ) : A) • dftMatrix (m i) ((↑(ζ i)⁻¹) : A))) := by
  have hinv (i : σ) : (diagonal (fun j : Fin (m i) => (w i : A)^j.val))⁻¹ =
      diagonal (fun j : Fin (m i) => (↑(w i)⁻¹ : A)^j.val) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal]
    simp [← mul_pow, ← diagonal_one]
  ext a b
  rw [Matrix.diagonal_mul]
  simp only [interpolationGrid, vandermonde_scaledNodes, Matrix.mul_inv_rev, hinv,
    inv_dftMatrix_of_unit_differences _ (hζ _) (hm _) (hd _), gridTensor,
    splitAddressScale, ← Finset.prod_inv_distrib, ← inv_pow, Units.coe_prod,
    Units.val_pow_eq_pow_val, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp [Matrix.kroneckerMap_apply, Matrix.diagonal_mul, mul_left_comm]


omit [Fintype σ] [DecidableEq σ] in
/-- Actual split nodes with their common binomial scales retained. The roots of unity
can be supplied directly in the long jet, for instance by `integralJet_axisRoot`. -/
theorem exists_scaledNodes_atZero (h : ℕ) (ρ β : σ → R) (m : σ → ℕ)
    (hm : ∀ i, IsUnit (m i : Jet R h)) (ζ : σ → (Jet R h)ˣ)
    (hζ : ∀ i, (ζ i)^(m i) = 1)
    (hd : ∀ i, Pairwise (fun j k : Fin (m i) =>
      IsUnit ((ζ i : Jet R h)^j.val - (ζ i : Jet R h)^k.val))) :
    ∃ (u : σ → Fin 2 → Jet R h) (w : σ → (Jet R h)ˣ),
      (∀ i j, (u i j)^2 = -u i j - specialize 0 h (C (ρ i)*X)) ∧
      (∀ i j, (scaledNodes (m i) (w i) (ζ i) j)^(m i) = specialize 0 h (binomial (β i))) ∧
      (∀ i, Pairwise (fun j k => IsUnit (u i j - u i k))) ∧
      (∀ i, Pairwise (fun j k => IsUnit
        (scaledNodes (m i) (w i) (ζ i) j - scaledNodes (m i) (w i) (ζ i) k))) := by
  let z : Jet R h := AdjoinRoot.root (X ^ h)
  let g := algebraMap R (Jet R h)
  have hx : specialize (0 : R) h X = z := by
    change aeval _ (taylor 0 X) = _
    rw [taylor_zero, aeval_X]
  have hc (x : R) : specialize (0 : R) h (C x) = g x := (specialize (0 : R) h).commutes x
  choose a b _ _ ea eb hab using fun i => quadraticRootsAtZero z (g (ρ i)) (jetParameter_nilpotent R h)
  choose w _ ew using fun i => binomialScalingAtZero z (g (β i)) (jetParameter_nilpotent R h)
    (m i) (hm i)
  refine ⟨fun i => ![a i, b i], w, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [map_mul, hc, hx]
    fin_cases j
    · change (a i)^2 = -a i - g (ρ i)*z
      linear_combination ea i
    · change (b i)^2 = -b i - g (ρ i)*z
      linear_combination eb i
  · intro i j
    have H : (ζ i : Jet R h)^(m i) = 1 := congrArg Units.val (hζ i)
    rw [scaledNodes, mul_pow, ← pow_mul, Nat.mul_comm j.val, pow_mul, H, one_pow, mul_one]
    simpa [binomial, hc, hx, g] using ew i
  · intro i j k hjk
    fin_cases j <;> fin_cases k <;> simp_all
    simpa using (hab i).neg
  · intro i j k hjk
    simpa [scaledNodes, mul_sub] using (w i).isUnit.mul (hd i hjk)

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
