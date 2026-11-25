import OAI.Computability.BorderVNP.PackedSewnFragmentProjection
import OAI.Computability.BorderVNP.CrossingParallelFrame

/-! # Joining the physical retained-wire and exterior-port fragment lists -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open Crossing VPVNP.VerifierNetwork

variable {σ : Type} [Fintype σ] {n m w : ℕ}
variable (left : Frame σ (Pin n w)) (right : Frame σ (Pin m w))

private def selectJoined (p : Pin (n+m) w) : Pin n w ⊕ Pin m w :=
  Fin.addCases (fun i => Sum.inl (i,p.2)) (fun j => Sum.inr (j,p.2)) p.1

/-- The complete physical operand list has the wire rectangle followed by the retained
port rectangle, with a common input valuation and exactly the sum of their gate counts. -/
noncomputable def joinFrame : Frame σ (Pin (n+m) w) := (parallelFrame left right).select selectJoined

theorem joinFrame_size : (joinFrame left right).size = left.size + right.size := by simp [joinFrame]

private def row {a : ℕ} (x : Pin a w → Bool) (i : Fin a) := if active x i then some (parse x i) else none

/-- The raw parser visits both real arrays without adding or dropping any enabled rows. -/
theorem joinFrame_list (x : σ → Bool) :
    list ((joinFrame left right).eval x) = list (left.eval x) ++ list (right.eval x) := by
  let z := (joinFrame left right).eval x
  have l (i : Fin n) (c : Column w) : z (Fin.castAdd m i,c) = left.eval x (i,c) := by
    simp [z,joinFrame,selectJoined]
  have r (i : Fin m) (c : Column w) : z (Fin.natAdd n i,c) = right.eval x (i,c) := by
    simp [z,joinFrame,selectJoined]
  have leftRow (i : Fin n) : row z (Fin.castAdd m i) = row (left.eval x) i := by
    unfold row active parse
    simp only [l]
  have rightRow (i : Fin m) : row z (Fin.natAdd n i) = row (right.eval x) i := by
    unfold row active parse
    simp only [r]
  change (List.finRange (n+m)).filterMap (row z) = (List.finRange n).filterMap (row (left.eval x)) ++
    (List.finRange m).filterMap (row (right.eval x))
  have indices : List.finRange (n+m) = (List.finRange n).map (Fin.castAdd m) ++ (List.finRange m).map (Fin.natAdd n) := by
    rw [← List.ofFn_id,List.ofFn_add,List.ofFn_eq_map,List.ofFn_eq_map]
    rfl
  rw [indices,List.filterMap_append,List.filterMap_map,List.filterMap_map]
  exact congrArg₂ (·++·) (congrArg (List.filterMap · (List.finRange n)) (funext leftRow))
    (congrArg (List.filterMap · (List.finRange m)) (funext rightRow))

/-- Filtering the common gate list to a real host commutes with the two physical passes. -/
theorem joinFrame_siteRuns (x : σ → Bool) (v : ℕ) :
    siteRuns v (list ((joinFrame left right).eval x)) =
      siteRuns v (list (left.eval x)) ++ siteRuns v (list (right.eval x)) := by
  simp only [joinFrame_list,siteRuns,List.filterMap_append]

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
