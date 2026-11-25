import OAI.Computability.BorderVNP.CubeCableChoice

/-! # Balancing by the increments of conditional bin means

At a fresh cell choose a candidate minimizing the scalar product of its new mean loads
with the old mean loads. The scalar product of the increment with the old vector is
then nonpositive. The initial target is constant on each load group and the group totals
are conserved, so its scalar product with the increment vanishes. Each squared increment
is bounded by the squared width incident to the cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.MeanChoice

open Balancing Finset
open scoped BigOperators

variable {C J : Type*} [Fintype C] [DecidableEq C] [Fintype J] {z : ℕ}

/-- Scalar product on the list of cable and delivery bins. -/
def dot (x y : J → ℝ) : ℝ := ∑ j, x j * y j

/-- Squared distance of the conditional mean vector from its initial value. -/
def energy (x target : J → ℝ) : ℝ := ∑ j, (x j - target j)^2

/-- The vector of actual conditional means of the load in each bin. -/
noncomputable def mean (load : J → (C → Fin (z+1)) → ℝ) (s : Finset C)
    (x : C → Fin (z+1)) : J → ℝ := fun j => conditioned (load j) s x

/-- Full candidate score. Subtracting the contribution of unaffected rows preserves its
least minimizer and gives the incident-row implementation. -/
noncomputable def trial (load : J → (C → Fin (z+1)) → ℝ) (s : Finset C)
    (x : C → Fin (z+1)) (c : C) (v : Fin (z+1)) : ℝ :=
  dot (mean load s x) (mean load (insert c s) (Function.update x c v))

/-- Process cells in public order, choosing the first minimizing label at every fresh cell. -/
noncomputable def follow (load : J → (C → Fin (z+1)) → ℝ) :
    List C → Finset C → (C → Fin (z+1)) → (C → Fin (z+1))
  | [], _, x => x
  | c :: cs, s, x => if c ∈ s then follow load cs s x else
    follow load cs (insert c s) (Function.update x c (firstMinimum (trial load s x c)))

private theorem dot_expected (load : J → (C → Fin (z+1)) → ℝ) (s : Finset C)
    (x : C → Fin (z+1)) (c : C) (hc : c ∉ s) :
    (𝔼 v, trial load s x c v) = dot (mean load s x) (mean load s x) := by
  unfold trial dot mean
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_expect, conditioned_insert _ _ _ hc]

/-- Choosing the minimum guarantees a nonpositive scalar product of the mean change with
the old loads, since averaging the candidate means gives back the old means. -/
theorem trial_le_self (load : J → (C → Fin (z+1)) → ℝ) (s : Finset C) (x : C → Fin (z+1))
    (c : C) (hc : c ∉ s) : trial load s x c (firstMinimum (trial load s x c)) ≤
      dot (mean load s x) (mean load s x) := by
  rw [← dot_expected load s x c hc]
  exact Finset.le_expect Finset.univ_nonempty fun v _ => firstMinimum_le _ v

/-- The exact algebraic change of squared distance. -/
theorem energy_change (x y target : J → ℝ) :
    energy y target = energy x target + 2*(dot x y-dot x x) -
      2*(dot target y-dot target x) + ∑ j, (y j-x j)^2 := by
  unfold energy dot
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _; ring

/-- The candidate update increases the squared error by at most the sum of squared
per-bin incidence bounds, including when a neighboring endpoint was already fixed. -/
theorem energy_step (load : J → (C → Fin (z+1)) → ℝ) (s : Finset C) (x : C → Fin (z+1))
    (c : C) (hc : c ∉ s) (target bound : J → ℝ)
    (conserve : ∀ v, dot target (mean load (insert c s) (Function.update x c v)) =
      dot target (mean load s x))
    (jump : ∀ v j, |mean load (insert c s) (Function.update x c v) j - mean load s x j| ≤ bound j) :
    let next := mean load (insert c s) (Function.update x c (firstMinimum (trial load s x c)))
    energy next target ≤ energy (mean load s x) target + ∑ j, (bound j)^2 := by
  intro next
  have hmin := trial_le_self load s x c hc
  change dot (mean load s x) next ≤ dot (mean load s x) (mean load s x) at hmin
  have htarget := conserve (firstMinimum (trial load s x c))
  change dot target next = _ at htarget
  have hsq : (∑ j, (next j-mean load s x j)^2) ≤ ∑ j, (bound j)^2 := by
    apply sum_le_sum
    intro j _
    have h := jump (firstMinimum (trial load s x c)) j
    change |next j-mean load s x j| ≤ bound j at h
    nlinarith only [sq_abs (next j-mean load s x j), mul_self_le_mul_self (abs_nonneg _) h]
  rw [energy_change (mean load s x) next target, htarget]
  linarith

/-- Accumulate the charges for each visited cell. Repeated names are skipped. -/
theorem follow_le (load : J → (C → Fin (z+1)) → ℝ) (cs : List C) (s : Finset C)
    (x : C → Fin (z+1)) (target : J → ℝ) (bound : C → J → ℝ)
    (conserve : ∀ s x c v, dot target (mean load (insert c s) (Function.update x c v)) =
      dot target (mean load s x))
    (jump : ∀ s x c v j, |mean load (insert c s) (Function.update x c v) j - mean load s x j| ≤ bound c j) :
    energy (mean load (cs.toFinset ∪ s) (follow load cs s x)) target ≤
      energy (mean load s x) target + (cs.map (fun c => ∑ j, (bound c j)^2)).sum := by
  induction cs generalizing s x with
  | nil => simp [follow]
  | cons c cs ih =>
    by_cases hc : c ∈ s
    · have he : (c::cs).toFinset ∪ s = cs.toFinset ∪ s := by ext; simp; grind
      rw [he, follow, ite_eq_left hc, List.map_cons, List.sum_cons]
      have hn : 0 ≤ ∑ j, (bound c j)^2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      linarith only [ih s x, hn]
    · have he : (c::cs).toFinset ∪ s = cs.toFinset ∪ insert c s := by ext; simp
      rw [he, follow, ite_eq_right hc, List.map_cons, List.sum_cons]
      have h₁ := energy_step load s x c hc target (bound c) (conserve s x c) (jump s x c)
      have h₂ := ih (insert c s) (Function.update x c (firstMinimum (trial load s x c)))
      dsimp only at h₁
      linarith

end Cube.MeanChoice

end BorderVNP
end Computability
end OAI
