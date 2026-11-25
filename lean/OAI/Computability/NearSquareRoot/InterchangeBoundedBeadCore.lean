import OAI.Computability.NearSquareRoot.InterchangeBeadBreeze
import OAI.Computability.NearSquareRoot.BoundedProgram

/-!
# Charging the joint radix command to a bead regime

The time allowance includes the width-dependent price. The peak space
allowance contains just the row count and the padded record length.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePayload
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
variable {I : Type} {r : Regime I}

theorem ceil_charge {a m : ℝ} {C : ℕ} (h : a ≤ C*m) :
    ⌈a⌉₊+1 ≤ (C+1)*(⌈m⌉₊+1) := by
  have z : ⌈a⌉₊ ≤ C*⌈m⌉₊ := Nat.ceil_le.mpr (by
    rw [Nat.cast_mul]
    exact h.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil m) (Nat.cast_nonneg C)))
  rw [Nat.add_mul,Nat.mul_add]
  omega

theorem bounded_padded_fare (N L u pad e : I → ℕ) (fit : ∀ i, u i ≤ L i)
    (dom : Dom r.scale pad) (α : ℝ) (hα : 0 ≤ α) (input output : I → Tree)
    (run : Space.BoundedTask (fun i => ⌈(N i : ℝ) * ((pad i + u i + 1 : ℕ) : ℝ) * (e i : ℝ)^α⌉₊)
      (fun i => N i * (pad i + u i + 1)) input output) :
    ∃ k : ℕ, Space.BoundedTask (fun i => ⌈runrate (Spindle.modes e (τ:=α)) r N L k i⌉₊)
      (fun i => ⌈mass r N L k i⌉₊) input output := by
  obtain ⟨t,C,ht⟩ := padded_fare N L u pad e fit dom α hα
  obtain ⟨s,D,hs⟩ := padded_fare N L u pad e fit dom 0 (le_refl _)
  refine ⟨t+s,run.bound (C+1) (D+1) ?_ ?_⟩
  · intro i
    apply ceil_charge
    exact (ht i).trans (mul_le_mul_of_nonneg_left
      (rate_higher i (Spindle.belly e hα i) (by omega : t ≤ t+s)) (Nat.cast_nonneg _))
  · intro i
    have hm : ((N i * (pad i + u i + 1) : ℕ) : ℝ) ≤ (D:ℝ)*mass r N L s i := by
      simpa only [Nat.cast_mul,Real.rpow_zero,runrate,Spindle.modes,mul_one] using hs i
    have z := ceil_charge (hm.trans (mul_le_mul_of_nonneg_left (mass_le (by omega : s ≤ t+s) i)
      (Nat.cast_nonneg _)))
    simpa only [Nat.ceil_natCast] using z

end InterchangePayload

end NearSquareRoot
end Computability
end OAI
