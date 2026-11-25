import OAI.LinearAlgebra.FiniteFourier.ProtectedTensorSynthesis
import OAI.LinearAlgebra.FiniteFourier.LocalKernelEmbedding

/-! # Heterogeneous tensors from the ternary kernel protecting two -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

/-- The ternary tensor compiler works for all integral factors of width
between four and the prescribed bound. The output constant is independent
of the entries and the number of factors. -/
theorem integerImageGridTensorEstimate_protected_ninth {d : ℕ} {β C : ℝ}
    (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hc : ∀ k : ℕ, (complexity (primeTransform 3 k
      ((AdjoinRoot.root (cyclotomic 9 (protectedRationals {2})))^3)) : ℝ) ≤
      C * (3 : ℝ)^k * (1+(k : ℝ))^β) :
    IntegerImageGridTensorEstimate (ProtectedCyclotomic {2} 9) 4 d β
      (((28 * (4 * d^2) + 1 : ℕ) : ℝ) * C) := by
  let E := ProtectedCyclotomic {2} 9
  let a : E := AdjoinRoot.root (cyclotomic 9 (protectedRationals {2}))
  let := protectedCyclotomic_isDomain {2} 9 (by decide)
  have ha : IsPrimitiveRoot a 9 := protectedCyclotomic_primitive {2} 9 (by decide)
  have h3 : IsUnit (3 : E) := by
    simpa using protectedCyclotomic_isUnit (L := {2}) 9 (d := 3) (by decide)
      (by simpa using (by decide : Nat.Coprime 2 3))
  have h9 : IsUnit (9 : E) := by convert h3.pow 2 using 1; norm_num
  have hu : IsUnit (a^3 - 1) := by
    simpa only [neg_sub] using (newtonFactor_isUnit ha (by simpa using h9)
      (by decide : 0 < 3) (by decide : 3 < 9)).neg
  have hζ : (a^3)^2 + a^3 + 1 = 0 := by
    apply hu.mul_left_cancel
    linear_combination ha.pow_eq_one
  apply integerImageGridTensorEstimate_of_unit_words (P := {2}) (t := 28) (p := 3)
    (ζ := a^3) (by simp [Nat.prime_two]) exists_unit_split_protected_ninth_at_two _ hβ hC
    (by simpa using hc)
  intro m hm _ T hc
  obtain ⟨c, h⟩ := hc
  have hw := (ringTernaryWord_unitShear (a^3) a hζ h3 ha.pow_eq_one hu c).kernelWord
  change KernelWord 3 (a^3) 28 (Matrix.transvection T.i T.j T.c)
  rw [← h]
  exact hw.transvection_of_card_le (by decide) T.hij (by simpa using (show 3 ≤ m by omega))

end FiniteFourier
end LinearAlgebra
end OAI
