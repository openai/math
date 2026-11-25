import Mathlib.Data.Nat.Size

/-! # The public horizon of the anchored price-game campaign -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Campaign

def inputSize (N R : ℕ) : ℕ := N + R.size + 1

/-- Compute the fixed 300th power by squaring the 150th power. -/
def rounds (N R : ℕ) : ℕ := (inputSize N R)^150 * (inputSize N R)^150

private theorem join_powers (x a b c : ℕ) (h : a+b=c) : x^a * x^b = x^c :=
  (Nat.pow_add x a b).symm.trans (congrArg (fun k : ℕ => x^k) h)

theorem rounds_eq (N R : ℕ) : rounds N R = (inputSize N R)^300 := by
  unfold rounds
  exact join_powers (inputSize N R) 150 150 300 rfl

end Campaign
end PriceGame
end LinearProgramming
end Optimization
end OAI
