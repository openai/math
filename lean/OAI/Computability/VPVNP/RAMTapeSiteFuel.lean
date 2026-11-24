import OAI.Computability.VPVNP.TallyConstants
import Mathlib.Tactic.DeriveFintype

/-! # Preparing the private fuel and choice bound on a finite stack machine

At input length `n` each call uses at most `n^u` private instructions. The
site uses a unary stack for this bound, one for its `2H-1` call credits and one
for the maximum `2H*(n^u+w)` bits in the canonical choice string. The fixed
parameter `u` affects only the finite control.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteFuel

open Tally

/-- Unary tallies for input length, bucket size, word width, instruction fuel, call credits,
choice bits, and arithmetic scratch. -/
inductive Port where
  | length | bucket | word | fuel | credit | choice | acc | sum | outer | tmp
  deriving DecidableEq

instance : Fintype Port := derive_fintype% Port

/-- Initial allowance-computation state containing only the input length, bucket capacity, and
word width. -/
def initial (n H w : ℕ) : State Port
  | .length => n
  | .bucket => H
  | .word => w
  | _ => 0

/-- Intermediate state with the input length raised to the fixed exponent on the fuel counter. -/
def powered (n H w u : ℕ) : State Port :=
  Function.update (initial n H w) .fuel (n^u)

/-- State with fuel `n^u`, call credits `2*H - 1`, and choice-string bound `2*H*(n^u + w)` in
unary. -/
def result (n H w u : ℕ) : State Port :=
  Function.update (Function.update (powered n H w u) .credit (2*H-1)) .choice (2*H*(n^u+w))

private def round : Program Port :=
  (Program.mul .fuel .length .acc .outer .tmp (by decide)).seq <|
  (Program.clear .fuel).seq <|
  (Program.copy .acc .fuel .tmp (by decide) (by decide) (by decide)).seq <|
  Program.clear .acc

/-- Unary program computing the fixed power of the input length by starting with one and
multiplying in each round. -/
def power : ℕ → Program Port
  | 0 => Program.addConst .fuel 1
  | u+1 => (power u).seq round

private theorem round_eval (n H w u : ℕ) : round.eval (powered n H w u) = powered n H w (u+1) := by
  funext i
  cases i <;> simp (config := { decide := true }) [round, powered, initial, pow_succ]

theorem power_eval (n H w u : ℕ) : (power u).eval (initial n H w) = powered n H w u := by
  induction u with
  | zero => funext i; cases i <;> simp (config := { decide := true }) [power, powered, initial]
  | succ u ih => change round.eval ((power u).eval _) = _; rw [ih, round_eval]

private theorem power_ready (n H w u : ℕ) : (power u).ready (initial n H w) := by
  induction u with
  | zero => trivial
  | succ u ih =>
    simp only [power, Program.seq_ready, ih, true_and, power_eval]
    simp (config := { decide := true }) [round, powered, initial]

private theorem round_work (n H w u : ℕ) :
    round.work (powered n H w u) = 12*n^u*n + 8*n^u + 6 := by
  simp (config := { decide := true }) [round, powered, initial]
  ring

theorem power_work_le (n H w u : ℕ) :
    (power u).work (initial n H w) ≤ (26*u+2)*(n+1)^u := by
  induction u with
  | zero => simp [power]
  | succ u ih =>
    rw [power, Program.seq_work, power_eval, round_work]
    have hpow : n^u ≤ (n+1)^u := Nat.pow_le_pow_left (Nat.le_succ n) u
    have hstep : (n+1)^u ≤ (n+1)^(u+1) := Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_succ u)
    have hmul : n^u*n ≤ (n+1)^(u+1) := by
      rw [pow_succ]
      exact Nat.mul_le_mul hpow (Nat.le_succ n)
    have h₁ : 1 ≤ (n+1)^(u+1) := Nat.one_le_pow _ _ (Nat.succ_pos n)
    have hprev := ih.trans (Nat.mul_le_mul_left _ hstep)
    have hfu := hpow.trans hstep
    rw [Nat.mul_succ, show 26*u+26+2 = (26*u+2)+26 by omega, Nat.add_mul]
    rw [Nat.mul_assoc 12]
    omega

private def decrement (src : Port) : Program Port where
  Q := _
  code := Routine.popCase src Routine.ret Routine.ret Routine.ret
  eval s := Function.update s src (s src - 1)
  work _ := 2
  ready _ := True
  spec s _ := by
    cases h : s src with
    | zero =>
      have hs := Routine.runs_popCase_empty src Routine.ret Routine.ret Routine.ret
        (s := encode s) (by simp [encode, h]) (Routine.runs_ret _)
      have he : Function.update s src (s src-1) = s := by
        rw [show s src-1 = s src by omega, Function.update_eq_self]
      rw [h] at he
      rw [he]
      exact hs
    | succ k =>
      have hs := Routine.runs_popCase_true src Routine.ret Routine.ret Routine.ret
        (s := encode s) (tail := List.replicate k true) (by simp [encode, h, List.replicate_succ])
        (Routine.runs_ret _)
      simpa only [h, Nat.add_sub_cancel, encode_update] using hs

private def bounds : Program Port :=
  let addBucket := Program.copy Port.bucket Port.credit Port.tmp (by decide) (by decide) (by decide)
  addBucket.seq <| addBucket.seq <|
  (Program.copy .fuel .sum .tmp (by decide) (by decide) (by decide)).seq <|
  (Program.copy .word .sum .tmp (by decide) (by decide) (by decide)).seq <|
  (Program.mul .credit .sum .choice .outer .tmp (by decide)).seq <|
  (decrement .credit).seq <| Program.clear .sum

/-- Compute private instruction fuel and use it to prepare the call-credit and choice-string
tallies. -/
def program (u : ℕ) : Program Port := (power u).seq bounds

theorem eval_program (n H w u : ℕ) : (program u).eval (initial n H w) = result n H w u := by
  change bounds.eval ((power u).eval (initial n H w)) = _
  rw [power_eval]
  funext i
  cases i <;> simp (config := { decide := true }) [result, bounds, powered, initial, decrement, two_mul]

theorem runs (n H w u : ℕ) : (program u).code.Runs ((program u).work (initial n H w))
    (encode (initial n H w)) (encode (result n H w u)) := by
  apply eval_program n H w u ▸ (program u).spec _
  simp only [program, Program.seq_ready, power_ready, true_and, power_eval]
  simp (config := { decide := true }) [bounds, powered, initial, decrement]

theorem bounds_work (n H w u : ℕ) :
    (program u).work (initial n H w) = (power u).work (initial n H w) +
      (22*H + 7*n^u + 7*w + 10*H*(n^u+w) + 13) := by
  simp only [program, Program.seq_work, power_eval, Nat.add_left_cancel_iff]
  simp (config := { decide := true }) [bounds, powered, initial, decrement]
  ring

/-- Under the live transcript bounds, constructing all three tallies takes
a fixed polynomial number of stack instructions. -/
theorem work_le (n H w u : ℕ) (hu : 1 ≤ u) (hH : H ≤ 2*n) (hw : w ≤ n) :
    (program u).work (initial n H w) ≤ (26*u+113)*(n+1)^(u+1) := by
  let B := (n+1)^(u+1)
  have one : 1 ≤ B := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hbase : n+1 ≤ (n+1)^u := Nat.le_self_pow (by omega) _
  have hp : (n+1)^u ≤ B := Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_succ u)
  have hn : n ≤ (n+1)^u := (Nat.le_succ n).trans hbase
  have hf : n^u ≤ (n+1)^u := Nat.pow_le_pow_left (Nat.le_succ n) u
  have hmul : H*(n^u+w) ≤ 4*B := by
    calc
      _ ≤ (2*(n+1)) * (2*(n+1)^u) := Nat.mul_le_mul (hH.trans (by omega)) (by omega)
      _ = _ := by dsimp [B]; rw [pow_succ]; ring
  have hpower := (power_work_le n H w u).trans (Nat.mul_le_mul_left _ hp)
  rw [bounds_work, show 26*u+113 = (26*u+2)+111 by omega, Nat.add_mul]
  change _ ≤ (26*u+2)*B + 111*B
  rw [Nat.mul_assoc 10 H]
  omega

end RAMTape.SiteFuel

end VPVNP
end Computability
end OAI
