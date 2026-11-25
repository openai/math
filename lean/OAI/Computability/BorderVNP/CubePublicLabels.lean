import OAI.Computability.BorderVNP.CubeScoreUpdates
import OAI.Computability.BorderVNP.CubeGreedy

/-!
# Executable rational public label choice

The public algorithm caches mean and variance for each cable or data bin.
Its inputs include lists of affected record IDs indexed by cell. A trial uses
the local updates and rational comparisons. Its output agrees with greedy
minimization of the full conditional real score.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Balancing

open Finset
open scoped BigOperators

variable {C J E : Type*} [Fintype C] [DecidableEq C] [Fintype J] [Fintype E]
  [DecidableEq E] {z : ℕ}

/-- A compressed bin of weighted descriptors and its target mean. -/
structure Bin (C L E : Type*) where
  /-- Endpoint prescriptions for each public descriptor. -/
  pattern : E → Pattern C L
  /-- Width represented by the descriptor. -/
  weight : E → ℚ
  /-- Mean before any cells are pinned. -/
  target : ℚ

/-- Index lists for the trial update at one cell of one bin. -/
structure RecordIDs (E : Type*) where
  /-- Mean records incident to the cell. -/
  mean : Finset E
  /-- Overlapping descriptor pairs with the cell at an endpoint. -/
  covariance : Finset (E × E)

/-- The incidence lists determined by the public endpoints. -/
def index (b : Bin C (Fin (z+1)) E) (c : C) : RecordIDs E :=
  ⟨incident (fun e ↦ (b.pattern e).sites) c,
   (overlapRecords (fun e ↦ (b.pattern e).sites)).filter fun e ↦
     c ∈ (b.pattern e.1).sites ∪ (b.pattern e.2).sites⟩

/-- Full squared-deviation objective of a collection of bins. -/
noncomputable def binDeviation (bins : J → Bin C (Fin (z+1)) E) (x : C → Fin (z+1)) : ℝ :=
  ∑ j, ((∑ e, ((bins j).weight e : ℝ)*hit ((bins j).pattern e) x) - (bins j).target)^2

/-- Initial or reference moments for the bins under a partial labeling. -/
def initialMoments (bins : J → Bin C (Fin (z+1)) E) (s : Finset C) (x : C → Fin (z+1)) :=
  fun j ↦ moments (bins j).pattern (bins j).weight s x

/-- Update the entire array of bin moments from its cell-indexed lists. -/
def nextMoments (bins : J → Bin C (Fin (z+1)) E) (idx : J → C → RecordIDs E)
    (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1)) (old : J → ℚ × ℚ) :=
  fun j ↦ updateMoments (bins j).pattern (bins j).weight s x c v
    (idx j c).mean (idx j c).covariance (old j)

/-- Evaluate the objective from the bin moments, with exact rational arithmetic. -/
def totalScore (bins : J → Bin C (Fin (z+1)) E) (cache : J → ℚ × ℚ) : ℚ :=
  ∑ j, score (bins j).target (cache j)

/-- Execute one least-minimizer scan per fresh cell. The mathematical finite functions
`idx` are the incidence tables supplied by the public reconstruction. -/
def publicLabels (bins : J → Bin C (Fin (z+1)) E) (idx : J → C → RecordIDs E) :
    List C → Finset C → (C → Fin (z+1)) → (J → ℚ × ℚ) → (C → Fin (z+1))
  | [], _, x, _ => x
  | c :: cs, s, x, old =>
    if c ∈ s then publicLabels bins idx cs s x old else
      let trials v := nextMoments bins idx s x c v old
      let v := firstMinimum (fun t ↦ totalScore bins (trials t))
      publicLabels bins idx cs (insert c s) (Function.update x c v) (trials v)

private theorem firstMinimum_ratCast (f : Fin (z+1) → ℚ) :
    firstMinimum (fun i ↦ (f i : ℝ)) = firstMinimum f := by
  have eq (l : List (Fin (z+1))) : l.argmin (fun i ↦ (f i : ℝ)) = l.argmin f := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [List.argmin_cons,List.argmin_cons,ih]
      cases l.argmin f <;> simp
  exact congrArg (fun o : Option (Fin (z+1)) ↦ o.getD 0) (eq _)

omit [DecidableEq E] in
private theorem totalScore_cast (bins : J → Bin C (Fin (z+1)) E)
    (s : Finset C) (x : C → Fin (z+1)) :
    (totalScore bins (initialMoments bins s x) : ℝ) = conditioned (binDeviation bins) s x := by
  simp only [totalScore,initialMoments,Rat.cast_sum,score_cast,conditioned,binDeviation]
  rw [Finset.expect_sum_comm]

/-- The finite rational algorithm with the public incidence tables outputs
exactly the same labeling as the full conditional expectation scan. -/
theorem publicLabels_eq (bins : J → Bin C (Fin (z+1)) E)
    (cs : List C) (s : Finset C) (x : C → Fin (z+1)) :
    publicLabels bins (fun j ↦ index (bins j)) cs s x (initialMoments bins s x) =
      chooseLabels (binDeviation bins) cs s x := by
  induction cs generalizing s x with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c ∈ s
    · simpa only [publicLabels,chooseLabels,ite_eq_left hc] using ih s x
    · have upd (v : Fin (z+1)) :
          nextMoments bins (fun j ↦ index (bins j)) s x c v (initialMoments bins s x) =
            initialMoments bins (insert c s) (Function.update x c v) := by
        funext j; exact updateMoments_eq _ _ _ _ _ _
      rw [publicLabels,chooseLabels,ite_eq_right hc,ite_eq_right hc]
      simp_rw [upd]
      have eq : firstMinimum (fun v ↦ conditioned (binDeviation bins) (insert c s) (Function.update x c v)) =
          firstMinimum (fun v ↦ totalScore bins (initialMoments bins (insert c s) (Function.update x c v))) := by
        simp_rw [← totalScore_cast]; exact firstMinimum_ratCast _
      rw [eq]
      exact ih _ _

end Cube.Balancing

end BorderVNP
end Computability
end OAI
