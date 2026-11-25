import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Collocation
import OAI.LinearAlgebra.SpectralBooks.RawPriceTransport

/-! # Endpoint costs for one exterior split

For each child both unchanged-mark costs are bounded by the price of the
middle exterior level. Moving the mark to the other endpoint instead costs
the upper level for DL or the lower level for LD. These statements include
vanishing children and coincident endpoints.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SiteTensor

variable {J : Type} {K : Type*} [Fintype J] [Nonempty J] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) {c : ℝ}

/-- The product log-price upper bound extends to zero tensors under the
convention that the price of the zero tensor is zero. -/
theorem rawLogPrice_mul_le (hc : 0 ≤ c) (X Y : Raw.{0} J K) :
    rawLogPrice φ c (X.mul Y) ≤ rawLogPrice φ c X + rawLogPrice φ c Y := by
  by_cases hx : X.coeff = 0
  · have h : (X.mul Y).coeff = 0 := funext fun x => by
      change X.coeff _ * Y.coeff _ = 0
      rw [hx]; exact zero_mul _
    rw [rawLogPrice_zero φ c _ h, rawLogPrice_zero φ c _ hx, zero_add]
    exact rawLogPrice_nonneg φ hc _
  by_cases hy : Y.coeff = 0
  · have h : (X.mul Y).coeff = 0 := funext fun x => by
      change X.coeff _ * Y.coeff _ = 0
      rw [hy]; exact mul_zero _
    rw [rawLogPrice_zero φ c _ h, rawLogPrice_zero φ c _ hy, add_zero]
    exact rawLogPrice_nonneg φ hc _
  exact (rawLogPrice_mul φ c X Y hx hy).le

namespace Relocation

variable {I Q H M : Type} {A : I → Type}
variable [Fintype I] [∀ i, Fintype (A i)] [Fintype Q] [Fintype H] [Fintype M]
variable [Nonempty H] [Nonempty M]

private theorem price_le_add_wire {D : Type} [Fintype D] [Nonempty D] (hc : 0 ≤ c)
    {X Y : Raw.{0} J K} (p q : J) (h : X.Restricts (Y.mul (wire K D p q))) :
    rawLogPrice φ c X ≤ rawLogPrice φ c Y +
      rawWireDistance φ c p q * Real.logb 2 (Fintype.card D) := by
  have hw : rawLogPrice φ c (wire K D p q) =
      rawWireDistance φ c p q * Real.logb 2 (Fintype.card D) :=
    rawLogPrice_group_diagonal φ ![p,q] c
  exact (rawLogPrice_mono φ hc h).trans ((rawLogPrice_mul_le φ hc Y _).trans_eq (by rw [hw]))

/-- Same-endpoint prices for an arbitrary single matrix acting on the mark. -/
theorem collocated_prices (hc : 0 ≤ c)
    (T : (∀ i, A i) → Q → K) (S : (∀ i, A i) → Q → H → H → K) (f : Q → Q → H → H → K)
    (hS : ∀ x i α β, S x i α β = ∑ j, T x j * f i j α β) (σ : I → J) (a b : J) :
    let child (p : J) := rawLogPrice φ c ((split A Q H S).group (placeSplit σ p a b))
    let parent (p : J) := rawLogPrice φ c ((marked A Q T).group (placeMark σ p))
    let t := rawWireDistance φ c a b
    child a ≤ parent a + t * Real.logb 2 (Fintype.card H) ∧
    child b ≤ parent b + t * Real.logb 2 (Fintype.card H) := by
  refine ⟨?_, price_le_add_wire φ hc a b (split_restricts_at_row T S f hS σ a b)⟩
  have h := price_le_add_wire φ hc b a (split_restricts_at_column T S f hS σ a b)
  rwa [rawWireDistance_symm φ c b a] at h

/-- All three endpoint bounds for the DL child. -/
theorem plus_endpoint_prices (hc : 0 ≤ c) (T : (∀ i, A i) → Q → K)
    (L : Q → M → H → K) (D : Q → H → M → K) (σ : I → J) (a b : J) :
    let child (p : J) := rawLogPrice φ c ((split A Q H (plusCoeff T L D)).group (placeSplit σ p a b))
    let parent (p : J) := rawLogPrice φ c ((marked A Q T).group (placeMark σ p))
    let t := rawWireDistance φ c a b
    child a ≤ parent a + t * Real.logb 2 (Fintype.card H) ∧
    child b ≤ parent b + t * Real.logb 2 (Fintype.card H) ∧
    child a ≤ parent b + t * Real.logb 2 (Fintype.card M) := by
  have h := collocated_prices φ hc T _ _ (plusCoeff_eq T L D) σ a b
  exact ⟨h.1, h.2, price_le_add_wire φ hc a b (plus_restricts_opposite T L D σ a b)⟩

/-- All three endpoint bounds for the LD child. -/
theorem minus_endpoint_prices (hc : 0 ≤ c) (T : (∀ i, A i) → Q → K)
    (D : Q → M → H → K) (L : Q → H → M → K) (σ : I → J) (a b : J) :
    let child (p : J) := rawLogPrice φ c ((split A Q H (minusCoeff T D L)).group (placeSplit σ p a b))
    let parent (p : J) := rawLogPrice φ c ((marked A Q T).group (placeMark σ p))
    let t := rawWireDistance φ c a b
    child a ≤ parent a + t * Real.logb 2 (Fintype.card H) ∧
    child b ≤ parent b + t * Real.logb 2 (Fintype.card H) ∧
    child b ≤ parent a + t * Real.logb 2 (Fintype.card M) := by
  have h := collocated_prices φ hc T _ _ (minusCoeff_eq T D L) σ a b
  refine ⟨h.1, h.2, ?_⟩
  have h' := price_le_add_wire φ hc b a (minus_restricts_opposite T D L σ b a)
  rwa [rawWireDistance_symm φ c b a] at h'

end Relocation
end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
