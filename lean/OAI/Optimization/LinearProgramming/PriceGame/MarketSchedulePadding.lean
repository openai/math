import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentSolver

/-! # Leading zero bits leave the binary transshipment unchanged -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment
variable {m g : ℕ}

theorem zero_schedule (k : ℕ) : schedule k (fun _ : Fin m => 0) = List.replicate k none := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [schedule, oddExperts, ih, List.replicate_succ', Nat.zero_div]

/-- Any additional high bits correspond solely to initial, all-zero doublings. -/
theorem padded_schedule (k d : ℕ) (qty : Fin m → ℕ) (hc : ∀ i, qty i < 2^k) :
    schedule (d+k) qty = List.replicate d none ++ schedule k qty := by
  induction k generalizing qty with
  | zero =>
    have hz : qty = fun _ => 0 := by funext i; have := hc i; simpa using this
    rw [hz, Nat.add_zero, zero_schedule]
    simp [schedule]
  | succ k ih =>
    have hh (i : Fin m) : qty i / 2 < 2^k := by
      have hi := hc i
      rw [pow_succ] at hi
      omega
    rw [Nat.add_succ, schedule, schedule, ih _ hh, List.append_assoc]

theorem double_initial (I : Input m g) : Input.double I.initial = I.initial := by
  simp [Input.double, Input.initial]

theorem initial_zero_highs (I : Input m g) (d : ℕ) :
    (List.replicate d none).foldl (operation Input.double I.unit) I.initial = I.initial := by
  induction d with
  | zero => rfl
  | succ d ih => simpa [List.replicate_succ, operation, double_initial] using ih

/-- The output agrees literally, not just by optimality, when the caller
uses an easier-to-compute width exceeding the largest input bit length. -/
theorem solveWithWidth_eq_of_le (I : Input m g) (qty : Fin m → ℕ) (k : ℕ) (h : Input.bits qty ≤ k) :
    I.solveWithWidth k qty = I.solve qty := by
  let d := k - Input.bits qty
  have hk : k = d + Input.bits qty := by dsimp [d]; omega
  have fits (i : Fin m) : qty i < 2 ^ Input.bits qty := by
    exact Nat.size_le.mp (Finset.le_sup (s := Finset.univ) (f := fun j : Fin m => (qty j).size)
      (Finset.mem_univ i))
  unfold Input.solve Input.solveWithWidth
  rw [hk, padded_schedule _ _ _ fits, List.foldl_append, initial_zero_highs]

end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
