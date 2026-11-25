import OAI.Computability.NearSquareRoot.CRTControlledBatches
import OAI.Computability.NearSquareRoot.InterchangeLogSlack

/-! # Guard width and free bits for a batch of controlled switches -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open Filter

/-- Enough high guard bits to pay for all keys in the stable exceptional sort. -/
def guardWidth (k : ℕ) := 7 + 2 * Nat.clog 2 (k+1)

theorem guardWidth_pays {k extent i : ℕ} (he : extent ≤ k) (hi : i ≤ k) :
    (3*extent+1)*(32*i) ≤ 2^(guardWidth k) := by
  have h := Nat.le_pow_clog (b := 2) (by decide) (k+1)
  calc
    _ ≤ 128 * (k+1)^2 := by
      have e := Nat.mul_le_mul (show 3*extent + 1 ≤ 4*(k+1) by omega)
        (show 32*i ≤ 32*(k+1) by omega)
      nlinarith
    _ ≤ 128 * (2^(Nat.clog 2 (k+1)))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)
    _ = _ := by simp [guardWidth, Nat.pow_add, Nat.mul_comm 2 (Nat.clog 2 (k+1)), Nat.pow_mul]

/-- Every fixed multiple of the address logarithm eventually fits in the free slots. -/
theorem eventually_clog_fits (d : ℕ) :
    ∀ᶠ k : ℕ in atTop, d * Nat.clog 2 (k+1) ≤ k := by
  let c := (1 + (Real.log 2)⁻¹)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have tends : Tendsto (fun k : ℕ => ((k+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have bound := tends.eventually (eventually_logSlack (2*d*c) (by positivity) 1
    (β := 0) (γ := 1) (by norm_num))
  filter_upwards [bound, eventually_ge_atTop (1:ℕ)] with k hk h₁
  change 2*d*c*(1+Real.log ((k+1 : ℕ) : ℝ))^1 * ((k+1 : ℕ) : ℝ)^(0:ℝ) ≤
    ((k+1 : ℕ) : ℝ)^(1:ℝ) at hk
  simp only [pow_one, Real.rpow_zero, Real.rpow_one, mul_one] at hk
  have hlog := clog_le_logScale (n := k+1) (by omega)
  change (((max 1 (Nat.clog 2 (k+1)) : ℕ) : ℝ)) ≤ c * (1+Real.log ((k+1 : ℕ) : ℝ)) at hlog
  have hc' : ((Nat.clog 2 (k+1) : ℕ) : ℝ) ≤ c * (1+Real.log ((k+1 : ℕ) : ℝ)) :=
    (Nat.cast_le.mpr (Nat.le_max_right ..)).trans hlog
  have hu := mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg (α := ℝ) d)
  push_cast at hk hu
  have hk' : 1 ≤ (k:ℝ) := by exact_mod_cast h₁
  exact_mod_cast (show (d:ℝ)*(Nat.clog 2 (k+1):ℝ) ≤ k from by nlinarith [hu])

/-- A fixed reciprocal fraction accommodates both the guarded chunks' guide width
and any fixed polynomial degree from the program's per-record overhead. -/
theorem eventually_batch_reserves (j d reserve : ℕ) :
    ∀ᶠ k : ℕ in atTop, 8*j*guardWidth k ≤ k ∧
      payloadBits d k + payloadBits reserve k ≤ k / (4*(j+1)) := by
  filter_upwards [eventually_clog_fits (72*j), eventually_clog_fits ((d+reserve)*(4*(j+1))),
    eventually_ge_atTop (1:ℕ)] with k hG hR hk
  have hp : 1 ≤ Nat.clog 2 (k+1) := by
    by_contra! h
    have b := Nat.le_pow_clog (b := 2) (by decide) (k+1)
    rw [show Nat.clog 2 (k+1)=0 by omega, Nat.pow_zero] at b
    omega
  constructor
  · unfold guardWidth
    have h := Nat.mul_le_mul_left (56*j) hp
    nlinarith
  · apply (Nat.le_div_iff_mul_le (by positivity)).2
    simpa only [payloadBits, ← Nat.add_mul, mul_assoc, Nat.mul_comm (Nat.clog 2 (k+1))] using hR

end Controlled

end NearSquareRoot
end Computability
end OAI
