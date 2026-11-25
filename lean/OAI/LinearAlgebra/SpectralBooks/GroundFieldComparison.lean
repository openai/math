import OAI.LinearAlgebra.SpectralBooks.ClassComparison
import OAI.LinearAlgebra.SpectralBooks.ComparisonPreorder
import OAI.LinearAlgebra.SpectralBooks.ComparisonStates
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.ComparisonBound

/-!
# Strict spectral comparison over every field

Adjoin the comparison `y ≤ x` to the restriction order. A normalized spectral
point for the enlarged order would contradict the strict price gap. The state
existence theorem therefore supplies a compression in that order, which pays
for the tensor powers in the original order.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped NNReal

/-- Strict separation by all spectral points forces one uniform comparison for
all positive powers. Boundedness by naturals and the unit lower bound on
nonzero elements are the rank hypotheses in Strassen's restriction semiring. -/
theorem powerComparison_of_spectral_lt {S : Type*} [CommSemiring S] [Preorder S]
    [IsOrderedAddMonoid S] [IsOrderedMonoid S] (hzero : ∀ z : S, 0 ≤ z)
    (hbound : ∀ z : S, ∃ n : ℕ, z ≤ (n : S)) (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    {x y : S} (hy : y ≠ 0)
    (hgap : ∀ f : normalizedSpectrum ((· ≤ ·) : S → S → Prop), f.val x < f.val y) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → x ^ n ≤ C • y ^ n := by
  classical
  by_contra hnone
  let R (a : S) : ℕ := (hbound a).choose
  have hno (D : S) (m : ℕ) (hm : 0 < m) : ¬ TradeLE x y (D + m) D :=
    fun h => hnone (powerComparison_of_tradeCompression hzero hbound (hunit y hy) hm h)
  obtain ⟨f, hf⟩ := @spectralPoint_of_no_compression S _ (tradePreorder x y) R
    (fun a => TradeLE.of_le (hzero a)) (fun a => TradeLE.of_le (hbound a).choose_spec)
    (fun _ _ _ _ h g => TradeLE.add h g) (fun z _ _ h => TradeLE.mul_left z h)
    (fun z hz => TradeLE.of_le (hunit z hz)) hno
  have point : f ∈ normalizedSpectrum ((· ≤ ·) : S → S → Prop) :=
    ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, fun a b h => hf.2.2.2.2 a b (TradeLE.of_le h)⟩
  exact (hgap ⟨f, point⟩).not_ge (hf.2.2.2.2 y x (TradeLE.reversed x y))

namespace SiteTensor

universe v
variable (I K : Type*) [Fintype I] [Nonempty I] [Field K]

/-- Strict comparison in Proposition 2.1, for local linear restriction of
actual finite tensors, over the given ground field. -/
theorem strictSpectralComparison : StrictSpectralComparison.{v} I K :=
  fun _ _ _ hy hgap => powerComparison_of_spectral_lt zero_le_tensor exists_le_natCast
    (fun _ => one_le_of_ne_zero) hy hgap

/-- The finite-family ordinary-sum expansion now has no external
strict-comparison hypothesis. -/
theorem expandedStrictComparison :
    ExpandedStrictComparison (Set.range (logPoint.{v} (I := I) (K := K)))
      (fun x y => classOfProduct x ≤ classOfProduct y) ClassOrdinarySum :=
  expandedStrictComparison_of_strict (strictSpectralComparison I K)

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
