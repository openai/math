import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI
/-! # Shared numerical tariff for compiling and evaluating one measured terminal factor -/

namespace Hierarchy.TraceReceiverVisitArithmetic

/-- Two independent native clocks (the selected compiler and the terminal
evaluator) share the expansive word-cube in the registered rate. -/
private theorem reserve {w c levels : ℕ} (large : max 64 c≤w) (count : levels≤w) :
    c*(4*levels+4)*(64*w+1)^3+(64*w+1)^3≤(16*w^10+1)^3 := by
  have big : 64≤w:=(Nat.le_max_left ..).trans large
  have rate : c≤w:=(Nat.le_max_right ..).trans large
  have one : 1≤w:=by omega
  have xx : 64*w+1≤w^3 := by
    have square:=Nat.mul_le_mul_right w big
    have cube:=Nat.mul_le_mul_right (w*w) (show 2≤w by omega)
    have positive:0<w*w:=Nat.mul_pos one one
    rw [pow_succ,pow_two]
    nlinarith
  have shape : 4*levels+4≤8*w:=by omega
  have k : c*(4*levels+4)+1≤9*w^2 := by
    have a:=Nat.mul_le_mul rate shape
    have b : 1≤w^2:=Nat.one_le_pow 2 w one
    nlinarith
  have small:=Nat.mul_le_mul k (Nat.pow_le_pow_left xx 3)
  have powers : w^11≤w^30 := Nat.pow_le_pow_right one (by decide)
  calc
    _ = (c*(4*levels+4)+1)*(64*w+1)^3 := by ring
    _ ≤ (9*w^2)*(w^3)^3 := small
    _ = 9*w^11 := by ring
    _ ≤ 4096*w^30 := Nat.mul_le_mul (by decide) powers
    _ = (16*w^10)^3 := by ring
    _ ≤ _ := Nat.pow_le_pow_left (by omega) 3

/-- The two charged portions are bounded jointly in the original S43 unit,
before multiplying by the actual inherited work at each terminal factor. -/
theorem joint_fee (rate coefficient : ℕ) {w levels ended stages : ℕ} (depth setup maps : ℕ)
    (large : max 64 rate ≤ w) (count : levels≤w) (endCount : ended≤ stages) :
    (ended+1)*(rate*(coefficient*(64*w+1)^3)*(4*levels+4)) +
        (10025+1016*depth+setup+maps)*((2*stages+1)*(coefficient*(64*w+1)^3)) ≤
      (10025+1016*depth+setup+maps)*((2*stages+1)*(coefficient*(16*w^10+1)^3)) := by
  let z:=10025+1016*depth+setup+maps
  let r:=rate*(4*levels+4)*(64*w+1)^3
  let x:=(64*w+1)^3
  have e : ended+1≤z*(2*stages+1) := by
    have pos : 0<z:=by dsimp [z];omega
    exact (by omega : ended+1≤2*stages+1).trans (Nat.le_mul_of_pos_left _ pos)
  calc
    _ = (ended+1)*(coefficient*r) + (z*(2*stages+1))*(coefficient*x) := by
      dsimp [z,r,x]
      ring
    _ ≤ (z*(2*stages+1))*(coefficient*r)+(z*(2*stages+1))*(coefficient*x) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ e) _
    _ = (z*(2*stages+1)*coefficient)*(r+x) := by ring
    _ ≤ _ := by
      have paid:=Nat.mul_le_mul_left (z*(2*stages+1)*coefficient) (reserve large count)
      simpa only [z,r,x,Nat.mul_assoc] using paid

end Hierarchy.TraceReceiverVisitArithmetic

end OAI
