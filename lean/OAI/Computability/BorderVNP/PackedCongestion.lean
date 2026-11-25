import OAI.Computability.BorderVNP.PackedRoutes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Pigeonhole

/-!
# Simultaneous congestion in the two-leg routing of Proposition 7.2

Each wire chooses its intermediate site uniformly and independently. A wire visits a given
site at most twice. Averaging the sum of exponential loads over all choices gives a single
routing that satisfies the logarithmic bound at every site.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

open Finset
open scoped Classical

private theorem exp_visit_le (a : ℕ) (ha : a ≤ 2) :
    Real.exp (a : ℝ) ≤ 1 + 4 * a := by
  interval_cases a
  · simp
  · norm_num
    linarith [Real.exp_one_lt_three]
  · norm_num
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1,
      mul_self_le_mul_self (Real.exp_pos 1).le Real.exp_one_lt_three.le]

private theorem site_moment_bound {W I : Type*} [Fintype W] [Fintype I] [Nonempty I]
    (a : W → I → ℕ) (ha : ∀ w i, a w i ≤ 2) (μ : ℝ)
    (hmean : (∑ w, (∑ i, (a w i : ℝ)) / Fintype.card I) ≤ μ) :
    (∑ c : W → I, Real.exp (∑ w, (a w (c w) : ℝ))) ≤
      (Fintype.card (W → I) : ℝ) * Real.exp (4 * μ) := by
  classical
  let m (w : W) := (∑ i, (a w i : ℝ)) / Fintype.card I
  have hcard : 0 < (Fintype.card I : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hm (w : W) : 0 ≤ m w := by dsimp [m]; positivity
  have hsum (w : W) :
      (∑ i, Real.exp (a w i : ℝ)) ≤ Fintype.card I * (1 + 4 * m w) := by
    calc
      _ ≤ ∑ i, (1 + 4 * (a w i : ℝ)) := sum_le_sum fun i _ ↦ exp_visit_le _ (ha w i)
      _ = _ := by
        rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
        dsimp [m]
        field_simp
  calc
    _ = ∏ w, ∑ i, Real.exp (a w i : ℝ) := by
      simp only [Real.exp_sum, Fintype.prod_sum]
    _ ≤ ∏ w, (Fintype.card I * (1 + 4 * m w)) :=
      prod_le_prod₀ (fun w _ ↦ sum_nonneg fun i _ ↦ (Real.exp_pos _).le) (fun w _ ↦ hsum w)
    _ = (Fintype.card (W → I) : ℝ) * ∏ w, (1 + 4 * m w) := by
      simp [prod_mul_distrib]
    _ ≤ (Fintype.card (W → I) : ℝ) * Real.exp (4 * μ) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply (Real.prod_one_add_le_exp_sum univ (fun w ↦ mul_nonneg (by norm_num) (hm w))).trans
      rw [← mul_sum]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmean (by norm_num))

/-- Independent intermediate choices can be fixed so all sites simultaneously have load
at most four times the largest expected load plus the natural logarithm of the site count. -/
theorem exists_low_congestion {W S I : Type*} [Fintype W] [Fintype S] [Fintype I]
    [Nonempty S] [Nonempty I] (load : W → S → I → ℕ) (μ : ℝ)
    (htwo : ∀ w s i, load w s i ≤ 2)
    (hmean : ∀ s, (∑ w, (∑ i, (load w s i : ℝ)) / Fintype.card I) ≤ μ) :
    ∃ choice : W → I, ∀ s, (∑ w, (load w s (choice w) : ℝ)) ≤
      4 * μ + Real.log (Fintype.card S) := by
  classical
  let moment (c : W → I) (s : S) := Real.exp (∑ w, (load w s (c w) : ℝ))
  let bound := (Fintype.card S : ℝ) * Real.exp (4 * μ)
  have htot : (∑ c, ∑ s, moment c s) ≤ ∑ _c : W → I, bound := by
    rw [sum_comm]
    calc
      _ ≤ ∑ _s : S, (Fintype.card (W → I) : ℝ) * Real.exp (4 * μ) :=
        sum_le_sum fun s _ ↦ site_moment_bound (fun w i ↦ load w s i)
          (fun w i ↦ htwo w s i) μ (hmean s)
      _ = _ := by simp [bound, mul_left_comm]
  obtain ⟨choice, _, hchoice⟩ := exists_le_of_sum_le univ_nonempty htot
  refine ⟨choice, fun s ↦ Real.exp_le_exp.mp ?_⟩
  calc
    _ = moment choice s := rfl
    _ ≤ ∑ j, moment choice j := single_le_sum (f := moment choice) (fun j _ ↦ (Real.exp_pos _).le) (mem_univ s)
    _ ≤ bound := hchoice
    _ = _ := by rw [Real.exp_add, Real.exp_log (Nat.cast_pos.mpr Fintype.card_pos), mul_comm]

/-- The two translated simple paths of every wire admit a simultaneous choice of intermediate
sites. The bound uses the per-endpoint multiplicity and the maximum number of sites per leg. -/
theorem exists_low_congestion_routes {G W : Type*} [Group G] [Fintype G] [DecidableEq G]
    [Fintype W] (path : G → Finset G) (left right : W → G) (k h : ℕ)
    (hleft : ∀ x, (univ.filter fun w ↦ left w = x).card ≤ k)
    (hright : ∀ x, (univ.filter fun w ↦ right w = x).card ≤ k)
    (hpath : ∀ u, (path u).card ≤ h) :
    ∃ middle : W → G, ∀ site : G, (∑ w, (routeVisit path left right w site (middle w) : ℝ))
      ≤ 8 * k * h + Real.log (Fintype.card G) := by
  obtain ⟨middle, hm⟩ := exists_low_congestion (routeVisit path left right) (2 * k * h : ℕ)
    (routeVisit_le_two path left right) (routeVisit_mean_le path left right k h hleft hright hpath)
  refine ⟨middle, fun site ↦ (hm site).trans_eq ?_⟩
  push_cast
  ring

end Packing

end BorderVNP
end Computability
end OAI
