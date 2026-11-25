import OAI.LinearAlgebra.FiniteFourier.PrimeMatrixRoot
import Mathlib.Data.Finsupp.Weight

/-! # Coefficient matrices for the predictor's pencil stages -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open MvPolynomial Matrix Finset
noncomputable section

private theorem affine_expansion {σ K : Type*} [CommRing K] [Fintype σ] (p : MvPolynomial σ K)
    (hp : p.totalDegree ≤ 1) :
    p = C (p.coeff 0) + ∑ a, C (p.coeff (Finsupp.single a 1)) * X a := by
  classical
  ext d
  by_cases hd : d = 0
  · subst d
    simp [coeff_C_mul, coeff_X]
  by_cases hsingle : ∃ i, d = Finsupp.single i 1
  · obtain ⟨a,rfl⟩ := hsingle
    simp [coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff, mul_ite, Ne.symm hd]
  · have hcoeff : p.coeff d = 0 := by
      apply notMem_support_iff.mp
      intro hm
      have hdeg := (le_totalDegree hm).trans hp
      have hpos : d.degree ≠ 0 := fun he => hd ((Finsupp.degree_eq_zero_iff d).mp he)
      exact hsingle ((Finsupp.sum_eq_one_iff d).mp (by
        change d.sum (fun _ k => k) ≠ 0 at hpos
        omega))
    have hne (a : σ) : Finsupp.single a 1 ≠ d := fun h => hsingle ⟨a, h.symm⟩
    simp [coeff_C_mul, coeff_X, hcoeff, Ne.symm hd, hne]

/-- Every polynomial matrix with affine entries is the same fixed scalar
pencil at every assignment of the variables. -/
theorem affinePencil_coefficients {I σ K : Type*} [CommRing K] [Fintype σ]
    (L : Matrix I I (MvPolynomial σ K)) (hL : ∀ x y, (L x y).totalDegree ≤ 1) :
    ∃ (A₀ : Matrix I I K) (A : σ → Matrix I I K), ∀ q : σ → K,
      L.map (eval q) = A₀ + ∑ a, q a • A a := by
  let A₀ : Matrix I I K := fun i j => (L i j).coeff 0
  let A : σ → Matrix I I K := fun a i j => (L i j).coeff (Finsupp.single a 1)
  refine ⟨A₀, A, fun q => ?_⟩
  ext i j
  rw [Matrix.add_apply, Matrix.sum_apply]
  have h := congrArg (eval q) (affine_expansion (L i j) (hL i j))
  change eval q (L i j) = (L i j).coeff 0 + ∑ a, q a * (L i j).coeff (Finsupp.single a 1)
  simpa [mul_comm] using h

/-- Write any affine query-power matrix with only strictly positive powers,
combining all zero-power coefficients into one constant matrix. -/
theorem exists_queryPencil_coefficients {K I : Type*} [CommRing K] {ℓ m : ℕ} [NeZero ℓ]
    {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (L : Matrix I I (MvPolynomial (Fin m × ZMod ℓ) K))
    (haff : ∀ i j, (L i j).totalDegree ≤ 1) :
    ∃ (A₀ : Matrix I I K) (A : Fin m → ZMod ℓ → Matrix I I K), ∀ k,
      L.map (eval (queryPowerValues hζ k)) =
        A₀ + ∑ j, ∑ a ∈ (univ : Finset (ZMod ℓ)).erase 0, queryPowerValues hζ k (j,a) • A j a := by
  classical
  obtain ⟨B,C,hBC⟩ := affinePencil_coefficients L haff
  refine ⟨B + ∑ j, C (j,0), fun j a => C (j,a), fun k => ?_⟩
  rw [hBC, Fintype.sum_prod_type]
  have hsplit (j : Fin m) :
      (∑ a, queryPowerValues hζ k (j,a) • C (j,a)) =
      C (j,0) + ∑ a ∈ (univ : Finset (ZMod ℓ)).erase 0, queryPowerValues hζ k (j,a) • C (j,a) := by
    rw [← sum_erase_add _ _ (mem_univ (0 : ZMod ℓ))]
    simp [queryPowerValues, add_comm]
  simp only [hsplit, sum_add_distrib, add_assoc]

/-- The common-width pencils for the shifted predictions in the form used
by a pencil stage. The query power indexed by zero is absorbed in `A₀`. -/
theorem exists_countPredictor_stages {K : Type*} [Field K] {ℓ b m D : ℕ} [NeZero ℓ] [NeZero b]
    {ζ ξ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hξ : IsPrimitiveRoot ξ b) (u : ℤ) (hD : D ≤ b) :
    ∃ (h : ℕ) (A₀ : (Fin m → ZMod ℓ) → Matrix (Fin h → Fin b) (Fin h → Fin b) K)
      (A : (Fin m → ZMod ℓ) → Fin m → ZMod ℓ → Matrix (Fin h → Fin b) (Fin h → Fin b) K),
      ∀ β k, (A₀ β + ∑ j, ∑ a ∈ (univ : Finset (ZMod ℓ)).erase 0,
        queryPowerValues hζ k (j,a) • A β j a) ^ b =
        eval (queryPowerValues hζ k) (countPredictor hζ β u D) • 1 := by
  classical
  obtain ⟨h,L,haff,hL,_⟩ := exists_countPredictor_pencils (m := m) hζ hξ u hD
  choose A₀ A hcoeff using fun β => exists_queryPencil_coefficients hζ (L β) (haff β)
  refine ⟨h, A₀, A, fun β k => ?_⟩
  rw [← hcoeff, specialize_matrix_root _ (hL β)]

end

end FiniteFourier
end LinearAlgebra
end OAI
