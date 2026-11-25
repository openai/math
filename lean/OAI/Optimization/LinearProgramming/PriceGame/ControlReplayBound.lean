import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignNative
import OAI.Optimization.LinearProgramming.PriceGame.CampaignRounds
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingPad

/-! The global fuel for the native reply dispatcher is evaluated on the physical
padded input word. The same polynomial covers both a first call and an arbitrary
tape presented to a continuation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
namespace Replay

open Polynomial

private noncomputable def fuelWith (a b c : ℕ) : Polynomial ℕ :=
  X^a * (C 5 * (C 2 * X)^b + (C 2 * (X + 1))^c) + 1

private theorem fuelWith_eval (a b c x : ℕ) :
    (fuelWith a b c).eval x = x^a * (5 * (2*x)^b + (2*(x+1))^c) + 1 := by
  simp only [fuelWith, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_one]

/-- A fixed degree-905 bound on source control transitions, in the encoded word length. -/
noncomputable def fuelPolynomial : Polynomial ℕ := fuelWith 300 602 605

theorem fuelPolynomial_eval (x : ℕ) :
    fuelPolynomial.eval x = x^300 * (5 * (2*x)^602 + (2*(x+1))^605) + 1 :=
  fuelWith_eval 300 602 605 x

theorem inputSize_le_ecPad (t : Tape) :
    Campaign.inputSize t.input.goods t.input.range ≤ (ecPad t).length := by
  rw [ecPad_length, encodeTape_length]
  unfold Campaign.inputSize
  omega

private theorem input_fuel_le {x s n : ℕ} (hs : s ≤ x) (hn : n ≤ x) (a b c : ℕ) :
    s^a * (5*(2*n)^b + (2*(n+1))^c) + 1 ≤ (fuelWith a b c).eval x := by
  rw [fuelWith_eval]
  exact Nat.add_le_add_right (Nat.mul_le_mul (Nat.pow_le_pow_left hs a)
    (Nat.add_le_add
      (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hn) b))
      (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hn 1)) c))) 1

set_option exponentiation.threshold 1024 in
/-- No bound on the reply tape is needed to choose the public fuel. -/
theorem controlClock_le_fuelPolynomial (t : Tape) :
    Driver.controlClock t.input.goods (Campaign.rounds t.input.goods t.input.range) ≤
      fuelPolynomial.eval (ecPad t).length := by
  let x := (ecPad t).length
  have hs : Campaign.inputSize t.input.goods t.input.range ≤ x := inputSize_le_ecPad t
  have hn : t.input.goods ≤ x := by unfold Campaign.inputSize at hs; omega
  have hn' : 0 < t.input.goods := Nat.zero_lt_of_lt t.input.anchor.isLt
  refine (Driver.controlClock_polynomial _ _ hn').trans ?_
  let cost (T : ℕ) := T * (5*(2*t.input.goods)^602 + (2*(t.input.goods+1))^605) + 1
  exact (congrArg cost (Campaign.rounds_eq _ _)).le.trans (input_fuel_le hs hn 300 602 605)

end Replay
end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
