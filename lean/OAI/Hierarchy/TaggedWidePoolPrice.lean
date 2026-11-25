import OAI.Hierarchy.TaggedShorterPacking
import OAI.Hierarchy.TaggedShorterBudget
import OAI.Hierarchy.TaggedGapScale

namespace OAI
/-! # The full hardwired candidate bank has linear word volume -/

noncomputable section
namespace Hierarchy.Tagged
open TaggedShorterPacking TaggedShorterBudget Filter

/-- Charge both the purchased modules and the maximum of the purchased
and candidate array lengths. Every candidate receives its entire supergroup
data width, including sites left idle by a selector. The dyadic width
ratio J and constants on c are uniform over a fixed type. -/
theorem pool_volume (g D B sites n : ℕ) (hb : 0<B) (half : B≤D) (bounded : D≤n)
    {C c c₀ U J : ℝ} (hC : 0≤C) (hc₀ : 0<c₀) (hc : c₀≤c) (upper : c≤U) (hJ : 0≤J)
    (count : g*D≤2*sites+D) (sitesVolume : (sites:ℝ)≤C*n)
    (dyadic : (D:ℝ)≤J*(2*B)) (small : 2*(B:ℝ)≤c*n) :
    let M := ⌈6*c*n/(2*(B:ℝ))⌉₊
    let S := max M (g*batches D B)
    (M:ℝ)*(2*B) ≤ (7*U)*n ∧
      (S:ℝ)*D ≤ (max 1 ((4*C+2)/(3*c₀))*J*(7*U))*n := by
  intro M S
  have moduleCap : (M:ℝ)*(2*B) ≤ (7*U)*n := by
    have paid := (installed_bounds (c:=c) (n:=(n:ℝ)) (hc₀.le.trans hc) (Nat.cast_nonneg _)
      (K:=2*B) (by omega) (by simpa using small)).2
    have up : 7*c*(n:ℝ) ≤ 7*U*n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left upper (by norm_num)) (Nat.cast_nonneg _)
    apply le_trans _ up
    simpa [M,installed] using paid
  have cand := candidate_modules g D B sites n hb half bounded hC hc₀ hc count sitesVolume
  push_cast at cand
  let L := max 1 ((4*C+2)/(3*c₀))
  have nonnegative : 0≤L := (show (0:ℝ)≤1 by norm_num).trans (le_max_left ..)
  have number : (S:ℝ) ≤ L*M := by
    change ((max M (g*batches D B):ℕ):ℝ) ≤ _
    push_cast
    apply max_le
    · exact le_mul_of_one_le_left (Nat.cast_nonneg M) (le_max_left ..)
    · exact cand.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (Nat.cast_nonneg M))
  refine ⟨moduleCap,?_⟩
  calc
    (S:ℝ)*D ≤ (L*M)*(J*(2*B)) :=
      mul_le_mul number dyadic (Nat.cast_nonneg D) (mul_nonneg nonnegative (Nat.cast_nonneg _))
    _ = (L*J)*((M:ℝ)*(2*B)) := by ring
    _ ≤ (L*J)*((7*U)*n) := mul_le_mul_of_nonneg_left moduleCap (mul_nonneg nonnegative hJ)
    _ = _ := by ring

/-- A native word of 2h+1 bits also holds a sum of polynomially many
bits per parent row, as needed by the exact integer pruning test and
the aggregate width counters. Its width remains linear in h. -/
theorem eventually_word_room (C d : ℝ) (hd : 0≤d) :
    ∀ᶠ h : ℕ in atTop, ∀ v : ℕ, (v:ℝ) ≤ (2:ℝ)^h*(C*(2*(h:ℝ))^d) → v < 2^(2*h+1) := by
  filter_upwards [GapScale.eventual_polynomial 0 C d hd] with h small v limit
  have fit : C*(2*(h:ℝ))^d ≤ (2:ℝ)^h := by simpa [gap] using small
  have n2 : (v:ℝ) ≤ (2:ℝ)^(2*h) := by
    rw [two_mul,pow_add]
    exact limit.trans (mul_le_mul_of_nonneg_left fit (by positivity))
  have full : (v:ℝ) < (2:ℝ)^(2*h+1) := by
    rw [pow_succ]
    exact n2.trans_lt (lt_mul_of_one_lt_right (by positivity) (by norm_num))
  exact_mod_cast full

end Hierarchy.Tagged

end
end OAI
