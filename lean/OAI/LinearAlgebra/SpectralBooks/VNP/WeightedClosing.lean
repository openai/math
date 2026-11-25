import Mathlib

/-! # Closing the weighted contraction at a boundary point

This file proves the concluding finite identities of Sections 10 and 11 of the VNP companion.
Each monomial carries a matrix depending linearly on its coefficient. The live program and
substituted contractions are compared only after all assignments contributing to a monomial
have been added. All identities hold in positive characteristic as well as characteristic zero.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace VNP

open MvPolynomial Matrix

noncomputable section

variable {K E ι σ τ : Type*} [Field K] [Field E] [Algebra K E]

/-- Apply the matrix weight for each monomial and add. The weights are indexed by exponents
and are linear over the prime field in the application to the signed witness. -/
def pinMatrix (W : (σ →₀ ℕ) → E →ₗ[K] Matrix ι ι K) (P : MvPolynomial σ E) : Matrix ι ι K :=
  (Finsupp.lsum K W) P.coeff

@[simp] theorem pinMatrix_monomial (W : (σ →₀ ℕ) → E →ₗ[K] Matrix ι ι K) (μ : σ →₀ ℕ) (a : E) :
    pinMatrix W (monomial μ a) = W μ a := by
  apply Finsupp.lsum_single

@[simp] theorem pinMatrix_sum {η : Type*} (W : (σ →₀ ℕ) → E →ₗ[K] Matrix ι ι K)
    (s : Finset η) (P : η → MvPolynomial σ E) :
    pinMatrix W (∑ j ∈ s, P j) = ∑ j ∈ s, pinMatrix W (P j) := by
  have he : (∑ j ∈ s, P j).coeff = ∑ j ∈ s, (P j).coeff := by
    ext; simp
  simp only [pinMatrix, he, map_sum]

/-- One designated nonzero residue makes the two finite contraction identities incompatible. -/
theorem weighted_diagonal_impossible [Fintype ι] [DecidableEq ι] (Ω Z : ι → K)
    (H : ι) (hH : Ω H ≠ 0) (M : Matrix ι ι K)
    (hrow : ∀ i, ∑ j, M i j * Ω j = Z i * Ω i)
    (hprogram : ∀ j, Z j = (if j = H then 1 else 0) + ∑ i, M i j) : False := by
  have h : (∑ j, Z j * Ω j) = Ω H + ∑ j, Z j * Ω j := calc
    _ = ∑ j, ((if j = H then 1 else 0) + ∑ i, M i j) * Ω j :=
      Finset.sum_congr rfl fun j _ => congrArg (· * Ω j) (hprogram j)
    _ = Ω H + ∑ j, ∑ i, M i j * Ω j := by
      simp [add_mul, Finset.sum_add_distrib, Finset.sum_mul, ite_mul]
    _ = _ := by rw [Finset.sum_comm (f := fun j i => M i j * Ω j)]; simp_rw [hrow]
  apply hH
  exact add_right_cancel (show Ω H + (∑ j, Z j * Ω j) = 0 + _ by rw [zero_add]; exact h.symm)

/-- The finite contraction argument of the border stretch theorem. `F i` is the polynomial
of queried entries before any wire shortening. Its substitution by `Y` has an exact expansion
into weighted assignments, after all wires have been shortened. The live query is `F i(c)`.
This statement allows coefficients of the assignments to lie in an extension field. -/
theorem boundary_program_impossible [Fintype ι] [DecidableEq ι]
    (W : (σ →₀ ℕ) → E →ₗ[K] Matrix ι ι K) (Ω : ι → K) (H : ι) (hH : Ω H ≠ 0)
    (Y : τ → MvPolynomial σ E) (c : τ → K) (F : ι → MvPolynomial τ K)
    (L : ℕ) (degree : ∀ i, ((aeval Y) (F i)).totalDegree ≤ L)
    (hpins : ∀ G : MvPolynomial τ K, ((aeval Y) G).totalDegree ≤ L →
      pinMatrix W ((aeval Y) G) *ᵥ Ω = eval c G • Ω)
    (A : ι → Type*) [∀ i, Fintype (A i)] (μ : (i : ι) → A i → σ →₀ ℕ)
    (a : (i : ι) → A i → E)
    (hexp : ∀ i, (aeval Y) (F i) = ∑ e, monomial (μ i e) (a i e))
    (hprogram : ∀ j, eval c (F j) = (if j = H then 1 else 0) +
      ∑ i, ∑ e, W (μ i e) (a i e) i j) : False := by
  let M : Matrix ι ι K := fun i j => pinMatrix W ((aeval Y) (F i)) i j
  apply weighted_diagonal_impossible Ω (fun i => eval c (F i)) H hH M
  · intro i
    exact congrFun (hpins (F i) (degree i)) i
  · intro j
    rw [hprogram j]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp [M, hexp, Matrix.sum_apply]

end
end VNP

end SpectralBooks
end LinearAlgebra
end OAI
