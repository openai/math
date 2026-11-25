import OAI.Computability.NearSquareRoot.PrecisionGridPassSpace

/-! # Indexed layer sweeps with separate time and workspace estimates -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Space

open IntegerMultiplication.Code
open IntegerMultiplication.Code.Task (forest)

/-- Execute a uniform layer program at every table. The table forest is traversed
once. Its total volume contributes once to time, and the live workspace only needs
the maximum of the layer costs in space. -/
theorem BoundedTask.indexedSweep {I : Type*} (d : I → ℕ) (table state : I → ℕ → Tree)
    (a V work : I → ℕ)
    (step : BoundedTask (fun x : (i : I) × Fin (d i) => a x.1)
      (fun x => work x.1)
      (fun x => .fork (table x.1 x.2.val) (state x.1 x.2.val))
      (fun x => state x.1 (x.2.val+1)))
    (hforest : ∀ i, (forest (table i) (List.range (d i))).count ≤ V i)
    (hstate : ∀ i j, j ≤ d i → (state i j).count ≤ V i) :
    BoundedTask (fun i => d i * a i + V i) (fun i => V i + work i)
      (fun i => .fork (forest (table i) (List.range (d i))) (state i 0))
      (fun i => state i (d i)) := by
  have passes := BoundedTask.indexedPasses d table state (fun i _ => a i) (fun i _ => work i)
    (fun i => V i + work i) step
    (fun i => (hforest i).trans (Nat.le_add_right ..))
    (fun i j h => (hstate i j h).trans (Nat.le_add_right ..))
    (fun i _ _ => Nat.le_add_left ..)
  apply passes.mono _ (fun _ => le_rfl)
  intro i
  have vol := hforest i
  rw [Task.forest_count, List.length_range] at vol
  have sums : (∑ j ∈ Finset.range (d i), (table i j).count) =
      costSum (fun j => (table i j).count) (List.range (d i)) := rfl
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul,
    Nat.mul_one, sums]
  omega

end Space

end NearSquareRoot
end Computability
end OAI
