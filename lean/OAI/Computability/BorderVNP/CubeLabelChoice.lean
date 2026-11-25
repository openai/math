import OAI.Computability.BorderVNP.CubeGreedy

/-!
# Deterministically balanced cell labels

The public greedy choice of labels realizes Lemma 8.2's two simultaneous budgets.
The statement works for any supplied visiting order covering the cells.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Balancing

open Finset

variable {C E A : Type*} [Fintype C] [DecidableEq C] [Fintype E] [Fintype A]

/-- The specific greedy output obeys the cable and incoming-data bounds simultaneously. -/
theorem chosen_labels_balanced (z : ℕ) (src dst : E → C) (recv : A → C)
    (cs : List C) (hcs : cs.toFinset = univ) (W : ℝ) (M : ℕ)
    (hne : ∀ e, src e ≠ dst e)
    (hcable : (Fintype.card E : ℝ) ≤ 2*W) (hdata : (Fintype.card A : ℝ) ≤ W)
    (hE : ∀ c, (univ.filter (fun e ↦ c ∈ ({src e,dst e} : Finset C))).card ≤ M)
    (hA : ∀ c, (univ.filter (fun b ↦ c = recv b)).card ≤ M)
    (hbudget : (z+1 : ℝ)^2 * (4*W*M) + (z+1) * (W*M) ≤ (W / (z+1 : ℝ)^2)^2) :
    let x := chooseLabels (deviation (L := Fin (z+1)) src dst recv) cs ∅ (fun _ ↦ 0)
    (∀ u v, load (cable src dst u v) x ≤ 4*W/(z+1 : ℝ)^2) ∧
      ∀ u, load (datum recv u) x ≤ 4*W/(z+1 : ℝ) := by
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    balanced_of_le_mean (L := Fin (z+1)) src dst recv W M hne hcable hdata hE hA
      (by simpa using hbudget) _ (chooseLabels_le_mean _ cs hcs (fun _ ↦ 0))

end Cube.Balancing

end BorderVNP
end Computability
end OAI
