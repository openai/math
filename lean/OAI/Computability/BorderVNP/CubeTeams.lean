import OAI.Computability.BorderVNP.CubeGreedy
import Mathlib.Data.Rat.Cast.Order

/-!
# Greedy assignment of symbol groups to teams

Section 8.2 assigns each group to a team of minimum current weight. We implement
the first-minimum tie rule and prove that every final weight is at most the mean
total weight plus the largest group weight. Rational weights accommodate the
raw-wire charge of one millionth.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

/-- The new load vector after assigning a group to a minimum-load team. -/
def assignGroup {r : ℕ} (x : Fin (r+1) → ℚ) (w : ℚ) : Fin (r+1) → ℚ :=
  fun j ↦ x j + if j = firstMinimum x then w else 0

/-- Traverse the group weights in the declared order. -/
def assignGroups {r : ℕ} (ws : List ℚ) (x : Fin (r+1) → ℚ) : Fin (r+1) → ℚ :=
  ws.foldl assignGroup x

private theorem total_assign {r : ℕ} (x : Fin (r+1) → ℚ) (w : ℚ) :
    (∑ j, assignGroup x w j) = (∑ j, x j) + w := by
  simp [assignGroup,Finset.sum_add_distrib]

private theorem sum_nonneg (ws : List ℚ) (hw : ∀ w ∈ ws, 0 ≤ w) : 0 ≤ ws.sum := by
  induction ws with
  | nil => simp
  | cons w ws ih => exact add_nonneg (hw w (by simp)) (ih (fun t ht ↦ hw t (by simp [ht])))

/-- Adding any list of nonnegative group weights preserves the bound on the
largest load above the mean. -/
theorem assignGroups_bound {r : ℕ} (ws : List ℚ) (x : Fin (r+1) → ℚ) (M : ℚ)
    (hw : ∀ w ∈ ws, 0 ≤ w ∧ w ≤ M)
    (hx : ∀ j, x j ≤ (∑ i, x i)/(r+1) + M) (j : Fin (r+1)) :
    assignGroups ws x j ≤ ((∑ i, x i)+ws.sum)/(r+1) + M := by
  induction ws generalizing x with
  | nil => simpa [assignGroups] using hx j
  | cons w ws ih =>
    obtain ⟨h0,hM⟩ := hw w (by simp)
    have hpos : (0 : ℚ) < r+1 := by positivity
    have hmin : x (firstMinimum x) ≤ (∑ i, x i)/(r+1) := by
      apply (le_div_iff₀ hpos).mpr
      simpa [mul_comm] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ firstMinimum_le x i)
    have step (i : Fin (r+1)) : assignGroup x w i ≤ (∑ k, assignGroup x w k)/(r+1) + M := by
      rw [total_assign,add_div]
      by_cases hi : i = firstMinimum x
      · rw [assignGroup,ite_eq_left hi,hi]
        linarith only [hmin,hM,div_nonneg h0 hpos.le]
      · rw [assignGroup,ite_eq_right hi,add_zero]
        linarith only [hx i,div_nonneg h0 hpos.le]
    have ht := ih (assignGroup x w) (fun t ht ↦ hw t (by simp [ht])) step
    simpa only [assignGroups,List.foldl_cons,List.sum_cons,total_assign,add_assoc] using ht

/-- Starting with empty teams, all final weights are at most the mean plus the
maximum admissible group weight. -/
theorem assigned_weight_le {r : ℕ} (ws : List ℚ) (M : ℚ) (hM : 0 ≤ M)
    (hw : ∀ w ∈ ws, 0 ≤ w ∧ w ≤ M) (i : Fin (r+1)) :
    assignGroups ws (fun _ ↦ 0) i ≤ ws.sum/(r+1) + M := by
  simpa using assignGroups_bound ws (fun _ : Fin (r+1) ↦ 0) M hw (by simpa using hM) i

end Cube

end BorderVNP
end Computability
end OAI
