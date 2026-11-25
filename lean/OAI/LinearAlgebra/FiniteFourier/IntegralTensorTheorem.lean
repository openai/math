import OAI.LinearAlgebra.FiniteFourier.BinaryTensorSynthesis
import OAI.LinearAlgebra.FiniteFourier.ProtectedTernaryTensors

/-! # Bounded-width integral tensor products from protected Fourier kernels

The two Fourier estimates suffice for all square local factors. Their ranks,
entries, and dimensions may vary, and the integer circuit works on every
abelian group, with each integer scaling or addition charged separately.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

/-- The circuit-size estimate preceding expansion into charged group operations. -/
theorem boundedGridTensorEstimate_of_protectedKernels {β B T : ℝ} (hβ : 0 ≤ β)
    (hB : 0 ≤ B) (hT : 0 ≤ T)
    (ternary : ∀ j : ℕ, (complexity (primeTransform 3 j
      ((AdjoinRoot.root (cyclotomic 9 (protectedRationals {2})))^3)) : ℝ) ≤
        T * (3 : ℝ)^j * (1+j : ℝ)^β)
    (binary : ∀ L : Finset ℕ, (∀ l ∈ L, Nat.Prime l) → (∀ l ∈ L, Odd l) →
      ∀ j : ℕ, (complexity (primeTransform 2 j (-1 : ProtectedCyclotomic L 8)) : ℝ) ≤
        B * (2 : ℝ)^j * (1+j : ℝ)^β) (d : ℕ) (hd : 2 ≤ d) :
    ∃ C > (0 : ℝ), BoundedGridTensorEstimate ℤ 2 d β C := by
  have ht := integerImageGridTensorEstimate_protected_ninth (d := d^2) hβ hT ternary
  have hb (L : Finset ℕ) (hL : ∀ l ∈ L, Nat.Prime l) (ho : ∀ l ∈ L, Odd l) :=
    protectedBinary_integerImageGridTensorEstimate (hi := d^2) hL ho (by decide : 2 ≤ 4)
      hβ hB (binary L hL ho)
  have H := integralTensorEstimate_of_protectedPairs hd hβ (by positivity) (by positivity) ht hb
  exact ⟨_, by positivity, H⟩

/-- The protected Fourier kernels imply companion Theorem 11.1, with its
uniform dependence on the maximum width and the exponent. -/
theorem integralTensorProducts_of_protectedKernels {β B T : ℝ} (hβ : 0 ≤ β)
    (hB : 0 ≤ B) (hT : 0 ≤ T)
    (ternary : ∀ j : ℕ, (complexity (primeTransform 3 j
      ((AdjoinRoot.root (cyclotomic 9 (protectedRationals {2})))^3)) : ℝ) ≤
        T * (3 : ℝ)^j * (1+j : ℝ)^β)
    (binary : ∀ L : Finset ℕ, (∀ l ∈ L, Nat.Prime l) → (∀ l ∈ L, Odd l) →
      ∀ j : ℕ, (complexity (primeTransform 2 j (-1 : ProtectedCyclotomic L 8)) : ℝ) ≤
        B * (2 : ℝ)^j * (1+j : ℝ)^β) (d : ℕ) (hd : 2 ≤ d) :
    ∃ C > (0 : ℝ), ∀ (k : ℕ) (n : Fin k → ℕ), (∀ i, 2 ≤ n i ∧ n i ≤ d) →
      ∀ A : (i : Fin k) → Matrix (Fin (n i)) (Fin (n i)) ℤ,
        ∃ (s : ℕ) (p : Circuit ℤ (∀ i, Fin (n i)) (∀ i, Fin (n i)) s),
          p.matrix = gridTensor A ∧
          (p.integerCost : ℝ) ≤ C * (↑(∏ i, n i) : ℝ) * (1 + (k : ℝ))^β ∧
          ∀ (G : Type*) [AddCommGroup G] (x : (∀ i, Fin (n i)) → G) (o : ∀ i, Fin (n i)),
            p.evalGroup x o = ∑ i, gridTensor A o i • x i := by
  obtain ⟨C, hC, H⟩ := boundedGridTensorEstimate_of_protectedKernels hβ hB hT ternary binary d hd
  exact ⟨_, by positivity, H.integerCircuit hβ⟩

end FiniteFourier
end LinearAlgebra
end OAI
