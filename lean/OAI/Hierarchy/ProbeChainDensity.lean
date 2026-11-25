import OAI.Hierarchy.ProbeDensity
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI
/-! # Summing the true H-chain scanner counts over the dyadic groups and signed marks -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

/-- This form keeps both the port count and the ceiling loss explicit. The chosen
fraction δ handles the former, and the sublinear number of actual groups handles
the latter. -/
theorem purchased_density {G C : Type*} [Fintype G] [Fintype C]
    (span : G → ℕ) (purchased left marked : G → C → ℕ) {H : ℕ}
    (hH : 0 < H) {δ β tiles : ℝ} (hδ : 0 ≤ δ)
    (actual : ∀ g c, purchased g c*H+left g c=marked g c)
    (maximal : ∀ g c, left g c < H*(2*⌈δ*(span g:ℝ)⌉₊))
    (many : β*tiles ≤ ∑ g, ∑ c, (marked g c:ℝ))
    (ports : (Fintype.card C:ℝ)*(2*H)*δ*(∑ g, (span g:ℝ)) ≤ β*tiles/4)
    (groups : (Fintype.card C:ℝ)*(2*H)*(Fintype.card G:ℝ) ≤ β*tiles/4) :
    β*tiles/(2*H) ≤ ∑ g, ∑ c, (purchased g c:ℝ) := by
  have realH : 0 < (H:ℝ) := by exact_mod_cast hH
  have rem (g : G) (c : C) : (left g c:ℝ) ≤ 2*H*δ*(span g:ℝ)+2*H := by
    have rounded := (Nat.ceil_lt_add_one (mul_nonneg hδ (Nat.cast_nonneg (span g)))).le
    have count : (left g c:ℝ) ≤ (H:ℝ)*(2*(⌈δ*(span g:ℝ)⌉₊:ℝ)) := by exact_mod_cast (maximal g c).le
    nlinarith only [count,mul_le_mul_of_nonneg_left rounded (show 0 ≤ 2*(H:ℝ) by positivity)]
  have sum := Finset.sum_le_sum (s:=Finset.univ) fun g _ =>
    Finset.sum_le_sum (s:=Finset.univ) fun c _ => rem g c
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at sum
  simp_rw [mul_add] at sum
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at sum
  have sizes : (∑ g, (Fintype.card C:ℝ)*(2*H*δ*(span g:ℝ))) =
      (Fintype.card C:ℝ)*(2*H)*δ*(∑ g, (span g:ℝ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro g _; ring
  rw [sizes] at sum
  have eq (g : G) (c : C) : (marked g c:ℝ)=(purchased g c:ℝ)*H+left g c := by exact_mod_cast (actual g c).symm
  simp_rw [eq,Finset.sum_add_distrib,←Finset.sum_mul] at many
  apply (div_le_iff₀ (show 0 < 2*(H:ℝ) by positivity)).2
  nlinarith only [many,sum,ports,groups]

end
end Hierarchy.AdaptiveProbe

end OAI
