import OAI.Computability.NearSquareRoot.InterchangeRepairRunComponents
import OAI.Computability.NearSquareRoot.InterchangeBQuestRepairBank

/-!
# Bounded oracle commands on grouped coefficient rows

The group and ungroup scans use the same layouts as the predictor and
spectral conversions. Their scan budgets add to the parent allowance.
The child time, data space and return-stack allowances pass through unchanged.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace Interchange.BRepairRun

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Loom InterchangeSpace SwapRepair
open RepairRun (Values Cell Store render groupCell lanesAt flattenGroup gatherGroup
  liveGroup liveBank predictorIndex)

variable {I Y K E D A B S U L : Type} {X : I → Type} {r : Regime I}
  {N l : I → ℕ} {job : Job Y} {zone : I → Y → Prop} {cell : Cell X K}

variable (store : Store r N l cell) (coord : E ≃ (D → K)) (basis : Series D)

include store in
theorem groupRuns {p : ℕ} (s : Series S) (u : Series U)
    (input : S ≃ A × D) (output : U ≃ B × D) (x : Values X A E) (y : Values X B E)
    (h : BHop job r N l zone p (together r.header (render cell s (lanesAt coord input x)))
      (render cell u (lanesAt coord output y))) :
    Runs job r N l zone (groupCell coord basis cell) p x y := by
  intro sa sb
  exact (h.preceded ((flattenGroup store coord basis sa s input x).right (Drive.started store.positive))).afterTask
    (gatherGroup store coord basis sb u output y)

include store in
theorem groupStep [Fintype D] {p : ℕ} (x y : (i : I) → X i → E)
    (step : ∀ d, BHop job r N l zone p
      (together r.header (fun i => cell i (fun k => coord (x i k) d)))
      (fun i => cell i (fun k => coord (y i k) d))) :
    BHop job r N l zone ((Fintype.card D * p : ℕ) : ℤ)
      (together r.header (fun i => groupCell coord basis cell i (x i)))
      (fun i => groupCell coord basis cell i (y i)) := by
  have h := BHop.collect store.positive basis basis (fun i d => cell i (fun k => coord (x i k) d))
    (fun i d => cell i (fun k => coord (y i k) d)) id (fun _ => p)
    (fun d => store.live (fun i k => coord (x i k) d))
    (fun d => store.live (fun i k => coord (y i k) d)) step
  change BHop job r N l zone _ (together r.header
    (stackRun (fun _ => basis) (fun i d => cell i (fun k => coord (x i k) d))))
    (stackRun (fun _ => basis) (fun i d => cell i (fun k => coord (y i k) d)))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul] using h


include store in
/-- A physical single-row certificate may present its basis streams as a flat
bank indexed by a dummy register and its component. -/
theorem oneGroupStep {p : ℕ} (s : Series (Unit × D)) (x y : (i : I) → X i → E)
    (h : BHop job r N l zone p
      (together r.header (render cell s (fun i t k => coord (x i k) t.2)))
      (render cell s (fun i t k => coord (y i k) t.2))) :
    BHop job r N l zone p (together r.header (fun i => groupCell coord basis cell i (x i)))
      (fun i => groupCell coord basis cell i (y i)) := by
  have source := liveGroup store coord basis x
  have get : Rip r N l (fun i => groupCell coord basis cell i (x i))
      (render cell s (fun i t k => coord (x i k) t.2)) := by
    apply Fatigue.dry s _ source
    intro t
    exact Fatigue.drill basis _ source t.2
  have out := liveBank store s (fun i (t : Unit × D) k => coord (y i k) t.2)
  have put : Rip r N l (render cell s (fun i t k => coord (y i k) t.2))
      (fun i => groupCell coord basis cell i (y i)) := by
    apply Fatigue.dry basis _ out
    intro d
    exact Fatigue.drill s _ out ((), d)
  exact (h.preceded (get.right (Drive.started store.positive))).afterTask put

include store in
theorem predictorRuns [Field K] {s m p : ℕ}
    (basis : Series (BasisIndex m)) (flat : Series ((Fin s × BasisIndex m) × L))
    (x y : (i : I) → RepairSchedule.Data K L (X i) s m)
    (h : BHop job r N l zone p
      (together r.header (render cell flat (RepairSchedule.streams x)))
      (render cell flat (RepairSchedule.streams y))) :
    Runs job r N l zone (groupCell (components K m).toEquiv basis cell) p
      (fun i (t : L × Fin s) => x i t.1 t.2) (fun i (t : L × Fin s) => y i t.1 t.2) :=
  groupRuns store (components K m).toEquiv basis flat flat (predictorIndex L s m) (predictorIndex L s m)
    (fun i (t : L × Fin s) => x i t.1 t.2) (fun i (t : L × Fin s) => y i t.1 t.2) h


include store in
/-- Return a grouped computation to the original independent scalar streams. -/
theorem ungroupRuns [Field K] {s m p : ℕ}
    (basis : Series (BasisIndex m)) (group : Series (L × Fin s))
    (flat : Series ((Fin s × BasisIndex m) × L))
    (x y : (i : I) → RepairSchedule.Data K L (X i) s m)
    (h : Runs job r N l zone (groupCell (components K m).toEquiv basis cell) p
      (fun i (t : L × Fin s) => x i t.1 t.2) (fun i (t : L × Fin s) => y i t.1 t.2)) :
    BHop job r N l zone p (together r.header (render cell flat (RepairSchedule.streams x)))
      (render cell flat (RepairSchedule.streams y)) := by
  have get := gatherGroup store (components K m).toEquiv basis group flat (predictorIndex L s m)
    (fun i (t : L × Fin s) => x i t.1 t.2)
  have put := flattenGroup store (components K m).toEquiv basis group flat (predictorIndex L s m)
    (fun i (t : L × Fin s) => y i t.1 t.2)
  exact ((h group group).preceded (get.right (Drive.started store.positive))).afterTask put

end Interchange.BRepairRun

end

end NearSquareRoot
end Computability
end OAI
