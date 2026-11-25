import OAI.LinearAlgebra.FiniteFourier.UniformKernelBound
import OAI.LinearAlgebra.FiniteFourier.PrimeBound

/-! # Integral tensor products of bounded-width local matrices

Companion Theorem 11.1 and its binary shear specialization, obtained by
running the prime Fourier construction over its two integral coefficient rings.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- Uniform gate bound for every list of integral square factors of widths
between two and `d`, independent of their entries and ranks. -/
theorem boundedGridTensorEstimate (d : ℕ) (hd : 2 ≤ d) {β : ℝ} (hβ : 1/2 < β) :
    ∃ C > (0 : ℝ), BoundedGridTensorEstimate ℤ 2 d β C :=
  boundedGridTensorEstimate_of_uniformKernels (by linarith) (uniformPrimeKernelBound 2 hβ)
    (uniformPrimeKernelBound 3 hβ) d hd

/-- Companion Theorem 11.1. One division-free integer circuit, with every
addition and prescribed scaling charged, computes the tensor of the local
matrices on every abelian group. -/
theorem integralTensorProducts (d : ℕ) (hd : 2 ≤ d) {β : ℝ} (hβ : 1/2 < β) :
    ∃ C > (0 : ℝ), ∀ (k : ℕ) (n : Fin k → ℕ), (∀ i, 2 ≤ n i ∧ n i ≤ d) →
      ∀ A : (i : Fin k) → Matrix (Fin (n i)) (Fin (n i)) ℤ,
        ∃ (s : ℕ) (p : Circuit ℤ (∀ i, Fin (n i)) (∀ i, Fin (n i)) s),
          p.matrix = gridTensor A ∧
          (p.integerCost : ℝ) ≤ C * (↑(∏ i, n i) : ℝ) * (1 + (k : ℝ))^β ∧
          ∀ (G : Type*) [AddCommGroup G] (x : (∀ i, Fin (n i)) → G) (o : ∀ i, Fin (n i)),
            p.evalGroup x o = ∑ i, gridTensor A o i • x i := by
  obtain ⟨C, hC, H⟩ := boundedGridTensorEstimate d hd hβ
  exact ⟨_, by positivity, H.integerCircuit (by linarith)⟩

/-- The integral tensor shear estimate used by the Fourier grid algorithm. -/
theorem integralShearBound {β : ℝ} (hβ : 1/2 < β) : ∃ C > (0 : ℝ), IntegralShearBound β C := by
  obtain ⟨C, hC, H⟩ := boundedGridTensorEstimate 2 le_rfl hβ
  exact ⟨C, hC, H.integralShearBound⟩

end FiniteFourier
end LinearAlgebra
end OAI
