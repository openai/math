import OAI.Computability.BorderVNP.CubeGroupWeightSchedule
import OAI.Computability.BorderVNP.CubeGroupWeightSemantic

/-! # Physical communication loads of the native team schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Physical

variable {l : Layout} {teams : TeamNative.Layout} {orig mem : ℕ → ℕ}
variable {n blocks b K h : ℕ} {D : LengthDeclaration n l.groups}
variable {A : Type*} [Fintype A] {label : Fin l.cells → Label (n+1) l.groups}
variable {recv : A → Fin l.cells} {w : A → ℕ}

/-- Rational joint cost of a symbol, using its actual incident shared lists,
incoming deliveries and original padded wire slots. -/
def jointCost (blocks b K h : ℕ) (D : LengthDeclaration n l.groups)
    (label : Fin l.cells → Label (n+1) l.groups) (recv : A → Fin l.cells) (w : A → ℕ) (s : Fin l.groups) : ℚ :=
  (incidentWidth blocks K h D s : ℚ) + (incomingWidth label recv w D.1 s : ℚ) +
    (groupRaw (blocks*(h*b)) D.1 s : ℚ)/1000000

/-- The group-weight word is an exact representation of its physical cost. -/
theorem ScheduleResult.weight_physical (result : ScheduleResult l teams orig mem)
    (image : PhysicalImage l orig blocks b K h D label recv w) (s : Fin l.groups) :
    TeamNative.unscale (mem (l.weights+s.val)) = jointCost blocks b K h D label recv w s := by
  rw [result.weights s.val s.isLt, image.weight_eq, TeamNative.unscale_scaledWeight]
  rfl

private theorem range_sum (f : ℕ → ℚ) (k : ℕ) :
    ((List.range k).map f).sum = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.range_succ,Finset.sum_range_succ,ih]

/-- The rational weight held by an actual physical team is bounded by the mean
plus the maximal physical symbol weight. -/
theorem ScheduleResult.team_physical_le (result : ScheduleResult l teams orig mem)
    (image : PhysicalImage l orig blocks b K h D label recv w) (M : ℚ) (hM : 0 ≤ M)
    (hgroup : ∀ s, jointCost blocks b K h D label recv w s ≤ M) (j : Fin (teams.r+1)) :
    TeamNative.unscale (mem (teams.totals+j.val)) ≤
      (∑ s, jointCost blocks b K h D label recv w s)/(teams.r+1) + M := by
  let f (k : ℕ) := TeamNative.unscale (l.weight orig k)
  have fe (s : Fin l.groups) : f s.val = jointCost blocks b K h D label recv w s := by
    simp only [f,image.weight_eq,TeamNative.unscale_scaledWeight,jointCost]
  have sum : ((List.range l.groups).map f).sum = ∑ s, jointCost blocks b K h D label recv w s := by
    rw [range_sum, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun s _ => fe s
  rw [result.totals,congrFun (TeamNative.loads_unscale teams.r (l.weight orig) l.groups) j,← sum]
  apply assigned_weight_le _ M hM
  intro t ht
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ht
  exact ⟨by unfold TeamNative.unscale; positivity,
    (fe ⟨k,List.mem_range.mp hk⟩).trans_le (hgroup _)⟩

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
