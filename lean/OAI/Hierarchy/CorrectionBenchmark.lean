import OAI.Hierarchy.Catalyst
import OAI.Hierarchy.CorrectionProducts

namespace OAI
/-! # The unit-catalyst benchmark

Moving every open bit to the center costs one unit per catalyst endpoint and
nothing for the data ports. This gives the benchmark even for zero widths.
-/

noncomputable section
namespace Hierarchy.CorrectionBenchmark

open LinearAlgebra.SpectralBooks Catalyst CorrectionProducts
open scoped BigOperators Classical

variable {F : Type*} [Field F] {k p : ℕ}

theorem card_wires (b : Fin k → ℕ) : (Fintype.card (Wire b) : ℝ) = ∑ j, (b j : ℝ) := by
  simp [Wire, Fintype.card_sigma]

/-- The ideal table and every table on the same binary ports lie below the
through-wire price. This argument applies to zero coefficients as well. -/
theorem price_le (P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k)))
    (b : Fin k → ℕ) (f : (Port p b → Bool) → F) :
    P.price (raw f) (sites b) ≤ 2 * (∑ j, (b j : ℝ)) := by
  have h := P.transport (raw f) (sites b) (fun _ => 0)
  rw [P.collapsed, Real.dist_eq, sub_zero] at h
  have d₁ (w : Wire b) (s : Bool) :
      dist (sites (p:=p) b (.inr (w,s))) 0 = 1 := by
    rcases w with ⟨j,t⟩
    cases s <;> simp [sites, dist_zero_right]
  have d₀ (i : Fin p) : dist (sites b (.inl i)) 0 = 0 := dist_self _
  have d (i : Wire b × Bool) : dist (sites (p:=p) b (.inr i)) 0 = 1 := d₁ i.1 i.2
  calc
    _ ≤ |P.price (raw f) (sites b)| := le_abs_self _
    _ ≤ _ := h
    _ = 2 * (∑ j, (b j : ℝ)) := by
      change (∑ i : Port p b, dist (sites b i) 0 * Real.logb 2 (Fintype.card Bool)) = _
      simp only [Fintype.card_bool, Nat.cast_ofNat,
        Real.logb_self_eq_one (by norm_num : (1:ℝ)<2), mul_one, Fintype.sum_sum_type,
        d₀, d, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul,
        Nat.cast_ofNat, card_wires]; ring

end Hierarchy.CorrectionBenchmark

end
end OAI
