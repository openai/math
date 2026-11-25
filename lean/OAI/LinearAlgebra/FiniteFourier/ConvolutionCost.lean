import OAI.LinearAlgebra.FiniteFourier.IntegralGridInputs
import OAI.LinearAlgebra.SpectralBooks.BorderCircuit

/-! # The minimum integral circuit size for formal polynomial multiplication

A finite circuit can compute all the coefficient polynomials simultaneously.
Consequently the least size is attained, including for the empty input.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks

private theorem exists_polynomial_family {R I : Type*} [CommRing R] (m : ℕ)
    (f : Fin m → MvPolynomial I R) :
    ∃ (r : ℕ) (p : MatrixMultiplication.Arithmetic.Program R I r) (out : Fin m → Fin r),
      ∀ i, registerPolynomial p (out i) = f i := by
  induction m with
  | zero => exact ⟨0, .nil, Fin.elim0, fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨a, p, u, hu⟩ := exists_registerPolynomial (f 0)
    obtain ⟨b, q, v, hv⟩ := ih (fun j => f j.succ)
    let out : Fin (m + 1) → Fin (a + b) := Fin.cases
      (MatrixMultiplication.Arithmetic.Program.oldIndex a b u)
      (fun j => MatrixMultiplication.Arithmetic.Program.newIndex a b (v j))
    refine ⟨a + b, p.append q, out, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (registerPolynomial_append_old p q u).trans hu
    · exact (registerPolynomial_append_new p q (v j)).trans (hv j)

private theorem exists_convolution_cost (n : ℕ) :
    ∃ (c r : ℕ) (p : MatrixMultiplication.Arithmetic.Program ℤ (Fin n ⊕ Fin n) r)
      (out : Fin (2*n-1) → Fin r), ComputesConvolution p out ∧ p.cost = c := by
  obtain ⟨r, p, out, hp⟩ := exists_polynomial_family (2*n-1)
    (fun d => convolutionCoefficient ℤ n d.val)
  exact ⟨p.cost, r, p, out, hp, rfl⟩

/-- Least count of binary arithmetic operations in an integral circuit computing
all coefficients of the product of two generic length-`n` polynomials. -/
noncomputable def integralConvolutionCost (n : ℕ) : ℕ := by
  classical exact Nat.find (exists_convolution_cost n)

/-- A single division-free program attains the minimum for all output coefficients. -/
theorem integralConvolutionCost_attained (n : ℕ) :
    ∃ (r : ℕ) (p : MatrixMultiplication.Arithmetic.Program ℤ (Fin n ⊕ Fin n) r)
      (out : Fin (2*n-1) → Fin r),
      ComputesConvolution p out ∧ p.cost = integralConvolutionCost n := by
  classical exact Nat.find_spec (exists_convolution_cost n)

theorem integralConvolutionCost_le {n r : ℕ}
    {p : MatrixMultiplication.Arithmetic.Program ℤ (Fin n ⊕ Fin n) r}
    {out : Fin (2*n-1) → Fin r} (hp : ComputesConvolution p out) :
    integralConvolutionCost n ≤ p.cost := by
  classical exact Nat.find_min' (exists_convolution_cost n) ⟨r, p, out, hp, rfl⟩

/-- A uniform estimate on minimum costs is equivalent to the existence of a
sufficiently small formal integral circuit at each positive input length. -/
theorem integralConvolutionBound_iff {β C : ℝ} :
    IntegralConvolutionBound β C ↔ ∀ n : ℕ, 0 < n →
      (integralConvolutionCost n : ℝ) ≤ C * n * (1 + Real.logb 2 n) ^ β := by
  constructor
  · intro h n hn
    obtain ⟨r, p, out, hp, hc⟩ := h n hn
    exact (Nat.cast_le (α := ℝ) |>.mpr (integralConvolutionCost_le hp)).trans hc
  · intro h n hn
    obtain ⟨r, p, out, hp, hc⟩ := integralConvolutionCost_attained n
    exact ⟨r, p, out, hp, hc ▸ h n hn⟩

end FiniteFourier
end LinearAlgebra
end OAI
