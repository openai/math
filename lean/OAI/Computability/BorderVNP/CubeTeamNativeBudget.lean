import OAI.Computability.BorderVNP.CubeTeamNativeAssignment

/-! # The paper's joint-weight bound on native team totals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamNative

/-- Every team total actually written by the public pass, measured in the paper's
units, is at most the mean weight plus the largest permitted group weight. -/
theorem Tables.team_weight_le {l : Layout} {ws orig mem : ℕ → ℕ}
    (t : Tables l ws orig l.groups mem) (M : ℚ) (hM : 0 ≤ M)
    (hw : ∀ i < l.groups, unscale (ws i) ≤ M) (j : Fin (l.r+1)) :
    unscale (mem (l.totals+j.val)) ≤
      ((List.range l.groups).map (fun i => unscale (ws i))).sum/(l.r+1)+M := by
  rw [t.totals, congrFun (loads_unscale l.r ws l.groups) j]
  apply assigned_weight_le _ M hM
  intro y hy
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hy
  exact ⟨by unfold unscale; positivity, hw i (List.mem_range.mp hi)⟩

/-- The owner stored for group `i` minimizes the current rational joint load, with
the paper's numerical tie rule. -/
theorem Tables.owner_eq_rational {l : Layout} {ws orig mem : ℕ → ℕ}
    (t : Tables l ws orig l.groups mem) {i : ℕ} (hi : i < l.groups) :
    mem (l.owners+i) = (firstMinimum (assignGroups
      ((List.range i).map (fun k => unscale (ws k))) (fun _ : Fin (l.r+1) => 0))).val := by
  rw [t.owners i hi, ← loads_unscale l.r ws i, firstMinimum_unscale]
  rfl

end Cube.TeamNative

end BorderVNP
end Computability
end OAI
