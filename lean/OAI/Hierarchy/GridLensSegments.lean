import OAI.Hierarchy.GridLensSites

namespace OAI
/-! # Directed segments of one mounted rail -/

namespace Hierarchy.GridLens
open scoped BigOperators
noncomputable section

/-- The first and last focus links, the interior crossings, and both halves of
each cell passage. In the last summand `false` denotes the incoming half. -/
abbrev Segment (n : ℕ) := (Unit ⊕ Fin n ⊕ Unit) ⊕ (Fin (n+1) × Bool)

variable {k n : ℕ}

/-- Each segment starts at its false endpoint and finishes at its true endpoint. -/
def segmentEnd (j : Fin k) (row : Fin k → Fin (n+1)) (R : ℝ) :
    Segment n → Bool → EuclideanSpace ℝ (Fin k)
  | .inl (.inl ()), false => point j 0 (-R)
  | .inl (.inl ()), true => cellPort (cellOnRail j row 0) j false
  | .inl (.inr (.inl t)), false => cellPort (cellOnRail j row t.castSucc) j true
  | .inl (.inr (.inl t)), true => cellPort (cellOnRail j row t.succ) j false
  | .inl (.inr (.inr ())), false => cellPort (cellOnRail j row (Fin.last n)) j true
  | .inl (.inr (.inr ())), true => point j 0 R
  | .inr (t, false), false => cellPort (cellOnRail j row t) j false
  | .inr (t, false), true => cellCenter (cellOnRail j row t)
  | .inr (t, true), false => cellCenter (cellOnRail j row t)
  | .inr (t, true), true => cellPort (cellOnRail j row t) j true

/-- The price of all elementary transport slots is the mounted rail length. -/
theorem sum_segment_dist (j : Fin k) (row : Fin k → Fin (n+1)) (R : ℝ) :
    (∑ s : Segment n, dist (segmentEnd j row R s false) (segmentEnd j row R s true)) =
      railCost j row R := by
  rw [railCost_eq_mounted]
  have incoming (t : Fin (n+1)) :
      dist (cellPort (cellOnRail j row t) j false) (cellCenter (cellOnRail j row t)) = 1 :=
    (dist_comm ..).trans (dist_cellCenter_port _ _ _)
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, segmentEnd,
    incoming, dist_cellCenter_port, dist_cellPort]
 ; ring

end
end Hierarchy.GridLens

end OAI
