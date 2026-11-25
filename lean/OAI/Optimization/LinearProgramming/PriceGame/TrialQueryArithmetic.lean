import OAI.Optimization.LinearProgramming.PriceGame.Complexity
import OAI.Optimization.LinearProgramming.PriceGame.MomentConstants
import OAI.Optimization.LinearProgramming.PriceGame.StatesMass

/-! A fixed polynomial bound for the recursive tree of a price trial. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

/-- The extra factor (2^l) accounts for the growing coordinate set at depth (l). -/
theorem queryRec_le (N r : ℕ) (f : ℕ → ℕ → ℕ)
    (h0 : ∀ l, f 0 l = 0)
    (hstep : ∀ k l, f (k+1) l ≤ 2*r*(f k (l+1) + N*2^l)) (fuel l : ℕ) :
    f fuel l ≤ N * 2^l * (6*r+1)^fuel := by
  induction fuel generalizing l with
  | zero => simp [h0]
  | succ k ih =>
    have hone : 1 ≤ (6*r+1)^k := Nat.one_le_pow k _ (by omega)
    have hlevel : N*2^l ≤ N*2^l*(6*r+1)^k := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (N*2^l) hone
    calc
      _ ≤ 2*r*(f k (l+1) + N*2^l) := hstep _ _
      _ ≤ 2*r*(N*2^(l+1)*(6*r+1)^k + N*2^l*(6*r+1)^k) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (ih _) hlevel)
      _ = (N*2^l*(6*r+1)^k) * (6*r) := by rw [pow_succ]; ring
      _ ≤ (N*2^l*(6*r+1)^k) * (6*r+1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
      _ = _ := by rw [pow_succ]; ring

theorem two_pow_trial_depth_le (N : ℕ) : 2^(States.Mass.depth N) ≤ 2*(N+1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · decide
  · rw [States.Mass.depth, pow_succ]
    have h := Nat.log2_self_le hN.ne'
    omega

private theorem six_times_probe_le (n : ℕ) : 6*(2^n+1)+1 ≤ 2^(n+4) := by
  rw [pow_add]
  change 6 * (2 ^ n + 1) + 1 ≤ 2 ^ n * 16
  have h : 0 < 2^n := Nat.pow_pos (by decide)
  omega

private theorem six_times_fixed_probe_le (p n : ℕ) (hp : p = 2^n+1) :
    6*p+1 ≤ (2 : ℕ)^(n+4) := hp ▸ six_times_probe_le n

private theorem pow_at_depth_le (N base k : ℕ) (hb : base ≤ 2^k) :
    base^(States.Mass.depth N) ≤ (2*(N+1))^k := by
  calc
    _ ≤ (2^k)^(States.Mass.depth N) := Nat.pow_le_pow_left hb _
    _ = (2^(States.Mass.depth N))^k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm k]
    _ ≤ _ := Nat.pow_le_pow_left (two_pow_trial_depth_le N) k

theorem probeBranchPow_le (N : ℕ) :
    (6*Moment.probes+1)^(States.Mass.depth N) ≤ (2*(N+1))^604 := by
  have hbase : 6*Moment.probes+1 ≤ 2^604 := by
    have h := six_times_fixed_probe_le Moment.probes 600 rfl
    have e : (2 : ℕ) ^ (600 + 4) = 2 ^ 604 :=
      congrArg (fun d : ℕ => 2^d) (show (600 : ℕ)+4 = 604 from rfl)
    exact h.trans_eq e
  exact pow_at_depth_le N (6*Moment.probes+1) 604 hbase

/-- One probe record per coordinate-price proposal, and no record at a leaf. -/
def probeLogBound (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2*r*(probeLogBound r k + 1)

theorem probeLogBound_succ_eq_nodeCount (r k : ℕ) :
    probeLogBound r k + 1 = Complexity.nodeCount (2*r) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 2*r*(probeLogBound r k + 1)+1 = 1+2*r*Complexity.nodeCount (2*r) k
    rw [ih, Nat.add_comm]

theorem probeLogBound_le_nodeCount (r k : ℕ) :
    probeLogBound r k ≤ Complexity.nodeCount (2*r) k := by
  rw [← probeLogBound_succ_eq_nodeCount]
  exact Nat.le_succ _

theorem probeLogBound_le (r k : ℕ) : probeLogBound r k ≤ (6*r+1)^k := by
  induction k with
  | zero => simp [probeLogBound]
  | succ k ih =>
    have hone : 1 ≤ (6*r+1)^k := Nat.one_le_pow k _ (by omega)
    calc
      _ ≤ 2*r*((6*r+1)^k + (6*r+1)^k) := Nat.mul_le_mul_left _ (Nat.add_le_add ih hone)
      _ = (6*r+1)^k * (4*r) := by ring
      _ ≤ (6*r+1)^k * (6*r+1) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := (pow_succ _ _).symm

theorem probeLogBound_polynomial (N : ℕ) :
    probeLogBound Moment.probes (States.Mass.depth N) ≤ (2*(N+1))^604 :=
  (probeLogBound_le ..).trans (probeBranchPow_le N)

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
