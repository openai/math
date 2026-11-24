import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # From exact midpoints to fractional points

In the geodesic-completion argument of Corollary 2.5, bisect a segment
repeatedly, keeping the half that contains the prescribed distance from its
left endpoint. The left endpoints are Cauchy and their limit has both
prescribed endpoint distances.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

open Filter
open scoped Topology

variable {X : Type*} [MetricSpace X]

/-- In a complete metric space with exact midpoints, every segment admits
a point at each fraction of its length. -/
theorem exists_fractionalPoint_of_midpoints [CompleteSpace X]
    (hm : ∀ a b : X, ∃ m, dist a m = dist a b / 2 ∧ dist m b = dist a b / 2)
    (a b : X) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ∃ z, dist a z = t * dist a b ∧ dist z b = (1 - t) * dist a b := by
  classical
  choose mid mid_left mid_right using hm
  let step (p : X × X) : X × X :=
    if dist a p.1 + dist p.1 p.2 / 2 ≤ t * dist a b then (mid p.1 p.2, p.2)
    else (p.1, mid p.1 p.2)
  let p : ℕ → X × X := Nat.rec (a, b) fun _ prev => step prev
  have bracket (n : ℕ) :
      dist a (p n).1 ≤ t * dist a b ∧
      dist (p n).2 b ≤ (1 - t) * dist a b ∧
      dist a (p n).1 + dist (p n).1 (p n).2 + dist (p n).2 b ≤ dist a b ∧
      dist (p n).1 (p n).2 = dist a b * (1 / 2 : ℝ) ^ n := by
    induction n with
    | zero =>
      change dist a a ≤ _ ∧ dist b b ≤ _ ∧ dist a a + dist a b + dist b b ≤ _ ∧ dist a b = _
      simp only [dist_self, zero_add, add_zero, pow_zero, mul_one, le_refl, and_true]
      exact ⟨mul_nonneg ht₀ dist_nonneg, mul_nonneg (sub_nonneg.mpr ht₁) dist_nonneg⟩
    | succ n ih =>
      obtain ⟨hl, hr, hpath, hlen⟩ := ih
      let l := (p n).1
      let r := (p n).2
      have hL := dist_triangle a l (mid l r)
      have hR := dist_triangle (mid l r) r b
      rw [mid_left] at hL
      rw [mid_right] at hR
      change dist a (step (l, r)).1 ≤ _ ∧ dist (step (l, r)).2 b ≤ _ ∧
        dist a (step (l, r)).1 + dist (step (l, r)).1 (step (l, r)).2 +
          dist (step (l, r)).2 b ≤ _ ∧ dist (step (l, r)).1 (step (l, r)).2 = _
      change dist a l + dist l r + dist r b ≤ _ at hpath
      change dist l r = _ at hlen
      by_cases hc : dist a l + dist l r / 2 ≤ t * dist a b
      · simp only [step, ite_eq_left hc, mid_right, pow_succ]
        exact ⟨hL.trans hc, hr, by linarith only [hL, hpath], by rw [hlen]; ring⟩
      · simp only [step, ite_eq_right hc, mid_left, pow_succ]
        exact ⟨hl, by linarith only [hc, hR, hpath], by linarith only [hR, hpath],
          by rw [hlen]; ring⟩
  have hstep (n : ℕ) : dist (p n).1 (p (n + 1)).1 ≤ dist a b * (1 / 2 : ℝ) ^ n := by
    change dist (p n).1 (step (p n)).1 ≤ _
    rw [← (bracket n).2.2.2]
    unfold step
    split
    · rw [mid_left]
      linarith only [dist_nonneg (x := (p n).1) (y := (p n).2)]
    · simp
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1 / 2 : ℝ) (dist a b) (by norm_num) hstep)
  have hleft : dist a z ≤ t * dist a b :=
    le_of_tendsto_of_tendsto' (tendsto_const_nhds.dist hz) tendsto_const_nhds
      (fun n => (bracket n).1)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hlen : Tendsto (fun n : ℕ => dist a b * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using hpow.const_mul (dist a b)
  have hright : dist z b ≤ (1 - t) * dist a b := by
    have bound := hlen.add_const ((1 - t) * dist a b)
    rw [zero_add] at bound
    refine le_of_tendsto_of_tendsto' (hz.dist tendsto_const_nhds) bound fun n => ?_
    have tri := dist_triangle (p n).1 (p n).2 b
    rw [(bracket n).2.2.2] at tri
    exact tri.trans (add_le_add_right (bracket n).2.1 _)
  exact ⟨z, by linarith only [hleft, hright, dist_triangle a z b],
    by linarith only [hleft, hright, dist_triangle a z b]⟩

end SpectralGeometry

end VPVNP
end Computability
end OAI
