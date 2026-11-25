import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Mean congestion of translated routes

In Proposition 7.2 the intermediate site is uniform in the finite tile group. For each displacement,
`path` records the sites on a chosen simple path from the identity. The two legs use the same
intermediate site. Independence between the legs is unnecessary.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

open Finset

variable {G W : Type*} [Group G] [Fintype G] [DecidableEq G] [Fintype W]

/-- Whether the path from `source` to `middle` visits `site`, as a natural number. -/
def legVisit (path : G → Finset G) (source site middle : G) : ℕ :=
  if source⁻¹ * site ∈ path (source⁻¹ * middle) then 1 else 0

/-- The two legs of a wire contribute separately at their common intermediate vertex. -/
def routeVisit (path : G → Finset G) (left right : W → G) (w : W) (site middle : G) : ℕ :=
  legVisit path (left w) site middle + legVisit path (right w) site middle

omit [Fintype G] [Fintype W] in
/-- A wire visits a specified site at most twice. -/
theorem routeVisit_le_two (path : G → Finset G) (left right : W → G) (w : W) (site middle : G) :
    routeVisit path left right w site middle ≤ 2 := by
  unfold routeVisit legVisit
  split <;> split <;> decide

private theorem leg_sum (path : G → Finset G) (site : G) :
    ∑ x : G, ∑ m : G, legVisit path x site m = ∑ u : G, (path u).card := by
  calc
    _ = ∑ x : G, ∑ u : G, if x⁻¹ * site ∈ path u then 1 else 0 := by
      apply sum_congr rfl
      intro x _
      exact Equiv.sum_comp (Equiv.mulLeft x⁻¹) (fun u => if x⁻¹ * site ∈ path u then (1 : ℕ) else 0)
    _ = ∑ u : G, ∑ x : G, if x⁻¹ * site ∈ path u then 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro u _
      apply Eq.trans (((Equiv.inv G).trans (Equiv.mulRight site)).sum_comp
        (fun y => if y ∈ path u then (1 : ℕ) else 0))
      simp

omit [Group G] in
private theorem endpoint_sum_le (endpoint : W → G) (k : ℕ)
    (h : ∀ x, (univ.filter fun w => endpoint w = x).card ≤ k) (cost : G → ℕ) :
    ∑ w, cost (endpoint w) ≤ k * ∑ x, cost x := by
  classical
  rw [← univ.sum_fiberwise endpoint (fun w => cost (endpoint w)), mul_sum]
  apply sum_le_sum
  intro x _
  calc
    _ = ∑ _w ∈ univ.filter (fun w => endpoint w = x), cost x := by
      apply sum_congr rfl
      intro w hw
      rw [(mem_filter.mp hw).2]
    _ = _ * cost x := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (h x)

/-- Averaging the two translated paths gives a per-site load at most `2*k*h`.
Here `k` bounds the multiplicity of each endpoint and `h` bounds the number of sites on a path. -/
theorem routeVisit_mean_le (path : G → Finset G) (left right : W → G) (k h : ℕ)
    (hleft : ∀ x, (univ.filter fun w => left w = x).card ≤ k)
    (hright : ∀ x, (univ.filter fun w => right w = x).card ≤ k)
    (hpath : ∀ u, (path u).card ≤ h) (site : G) :
    (∑ w : W, (∑ m : G, (routeVisit path left right w site m : ℝ)) / Fintype.card G)
      ≤ (2 * k * h : ℕ) := by
  have hp : ∑ u, (path u).card ≤ Fintype.card G * h := by
    simpa using (sum_le_sum (s := univ) (fun u _ => hpath u))
  have hs (endpt : W → G) (he : ∀ x, (univ.filter fun w => endpt w = x).card ≤ k) :
      ∑ w, ∑ m, legVisit path (endpt w) site m ≤ k * (Fintype.card G * h) := by
    exact (endpoint_sum_le endpt k he (fun x => ∑ m, legVisit path x site m)).trans
      (by rw [leg_sum path site]; exact Nat.mul_le_mul_left k hp)
  have hb : ∑ w, ∑ m, routeVisit path left right w site m ≤ 2 * k * h * Fintype.card G := by
    simp only [routeVisit, sum_add_distrib]
    have hl := hs left hleft
    have hr := hs right hright
    nlinarith
  rw [← sum_div, div_le_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)]
  exact_mod_cast hb

end Packing

end BorderVNP
end Computability
end OAI
