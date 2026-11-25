import OAI.Computability.BorderVNP.CubeFirstMinimum
import OAI.Computability.BorderVNP.CubeTeams

/-! # Integer words for the rational team loads of Section 8.2 -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamNative

/-- Section 8.2's joint group weight, expressed in millionths of one word. -/
def scaledWeight (shared data raw : ℕ) : ℕ := 1000000*(shared+data)+raw

/-- Interpret the stored integer in the original rational units. -/
def unscale (x : ℕ) : ℚ := (x : ℚ)/1000000

/-- The integer weight records the exact raw-load charge. -/
theorem unscale_scaledWeight (shared data raw : ℕ) :
    unscale (scaledWeight shared data raw) = shared+data+(raw : ℚ)/1000000 := by
  simp [unscale,scaledWeight]
  ring

/-- Positive rescaling preserves the same minimizing team, including ties. -/
theorem firstMinimum_unscale {r : ℕ} (f : Fin (r+1) → ℕ) :
    firstMinimum (fun j => unscale (f j)) = firstMinimum f := by
  apply (firstMinimum_eq_iff _ _).2
  obtain ⟨hm,hfirst⟩ := (firstMinimum_eq_iff f _).1 rfl
  have he (a b : ℕ) : unscale a ≤ unscale b ↔ a ≤ b := by
    simp [unscale,div_le_div_iff_of_pos_right (by norm_num : (0:ℚ) < 1000000)]
  exact ⟨fun j => (he _ _).2 (hm j), fun j hj => hfirst j ((he _ _).1 hj)⟩

/-- Team loads after the first `k` groups, measured in millionths of a word. -/
def loads (r : ℕ) (ws : ℕ → ℕ) : ℕ → Fin (r+1) → ℕ
  | 0 => fun _ => 0
  | k+1 => let x := loads r ws k; let team := firstMinimum x
           Function.update x team (x team + ws k)

/-- Public owner recorded when group `k` enters the schedule. -/
def owner (r : ℕ) (ws : ℕ → ℕ) (k : ℕ) := firstMinimum (loads r ws k)

/-- No intermediate load exceeds the total charge of the groups already assigned. -/
theorem loads_le (r : ℕ) (ws : ℕ → ℕ) (k : ℕ) (j : Fin (r+1)) :
    loads r ws k j ≤ ∑ i ∈ Finset.range k, ws i := by
  induction k generalizing j with
  | zero => simp [loads]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases h : j = owner r ws k
    · subst j
      simpa [loads,owner] using Nat.add_le_add_right (ih (owner r ws k)) (ws k)
    · simpa [loads,owner,show j ≠ firstMinimum (loads r ws k) from h] using
        (ih j).trans (Nat.le_add_right _ _)

/-- The computed team totals agree, in the original units, with the paper's
greedy traversal in public symbol order. -/
theorem loads_unscale (r : ℕ) (ws : ℕ → ℕ) (k : ℕ) :
    (fun j => unscale (loads r ws k j)) =
      assignGroups ((List.range k).map (fun i => unscale (ws i))) (fun _ : Fin (r+1) => 0) := by
  induction k with
  | zero => simp [loads,unscale,assignGroups]
  | succ k ih =>
    rw [List.range_succ, List.map_append]
    simp only [assignGroups, List.foldl_append, List.map_cons, List.map_nil, List.foldl_cons,
      List.foldl_nil]
    rw [show ((List.range k).map (fun i => unscale (ws i))).foldl assignGroup
        (fun _ : Fin (r+1) => 0) = _ from ih.symm]
    funext j
    by_cases h : j = firstMinimum (loads r ws k)
    · simp [loads,assignGroup,firstMinimum_unscale,h]
      simp [unscale,add_div]
    · simp [loads,assignGroup,firstMinimum_unscale,h]

end Cube.TeamNative

end BorderVNP
end Computability
end OAI
