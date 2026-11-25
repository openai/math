import OAI.LinearAlgebra.FiniteFourier.BinaryTensorLocal
import OAI.LinearAlgebra.FiniteFourier.LocalKernelEmbedding
import OAI.LinearAlgebra.FiniteFourier.ProtectedTensorSynthesis

/-! # Bounded-width integral tensors over the protected eighth-root extension -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- Each transvection with unit coefficient on a chosen pair of registers
in the protected eighth-root extension uses seven synchronized slots. -/
theorem protectedEighth_unitTransvection {P : Finset ℕ} (hodd : ∀ q ∈ P, Odd q)
    {m : ℕ} (hm : 2 ≤ m) (T : Matrix.TransvectionStruct (Fin m) (ProtectedCyclotomic P 8))
    (hT : IsUnit T.c) :
    KernelWord 2 (-1 : ProtectedCyclotomic P 8) 7 T.toMatrix := by
  let : IsDomain (ProtectedCyclotomic P 8) := protectedCyclotomic_isDomain P 8 (by decide)
  have h₂ : IsUnit (2 : ProtectedCyclotomic P 8) := protectedCyclotomic_isUnit 8 (d := 2)
    (by decide) (fun q hq => Nat.coprime_two_right.mpr (hodd q hq))
  have h := protectedHadamard_unitTransvection_kernelWord
    (protectedCyclotomic_primitive P 8 (by decide)) h₂ hT.unit
  rw [IsUnit.unit_spec] at h
  exact h.transvection_of_card_le (by decide) T.hij (by simpa using hm)

/-- A uniform binary Fourier tensor estimate gives a bound for all integral
local matrices on widths between `lo` and `hi`. The resulting constant is
independent of their entries, their count, and the protected odd primes. -/
theorem protectedBinary_integerImageGridTensorEstimate {P : Finset ℕ}
    (hP : ∀ q ∈ P, Nat.Prime q) (hodd : ∀ q ∈ P, Odd q) {lo hi : ℕ} (hlo : 2 ≤ lo)
    {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hc : ∀ k : ℕ, (complexity (primeTransform 2 k (-1 : ProtectedCyclotomic P 8)) : ℝ) ≤
      C * (2 : ℝ)^k * (1 + (k : ℝ))^β) :
    IntegerImageGridTensorEstimate (ProtectedCyclotomic P 8) lo hi β
      (((7 * (4 * hi^2) + 1 : ℕ) : ℝ) * C) :=
  integerImageGridTensorEstimate_of_unit_words hP (exists_unit_split_protected_eighth hP hodd)
    (fun _ hm _ T => protectedEighth_unitTransvection hodd (hlo.trans hm) T) hβ hC hc

end FiniteFourier
end LinearAlgebra
end OAI
