import OAI.Computability.NearSquareRoot.CRTControlledPrefixStage
import OAI.Computability.NearSquareRoot.ScheduleRegisterAlignEffectiveTask

/-! # Recharging named prefix traversal clocks at a common descriptor degree -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PrefixCommand

open IntegerMultiplication Code Strip

variable {X : Type} {r : Regime X} {n w : X → ℕ}

/-- Raising the real clock of a concrete command retains that command on tape. -/
theorem price {c : Cmd} {u v : X → Tree} {a b : X → ℝ} (C : ℕ)
    (h : EffectiveTask.Runs c (fun i => ⌈a i⌉₊) u v) (ht : ∀ i, a i ≤ C*b i) :
    EffectiveTask.Runs c (fun i => ⌈b i⌉₊) u v := by
  apply h.bound (C+1)
  intro i
  have step : a i ≤ (C*⌈b i⌉₊ : ℕ) := by
    push_cast
    exact (ht i).trans (mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg C))
  have := Nat.ceil_le.mpr step
  rw [Nat.succ_mul,Nat.mul_succ]; omega

/-- Polynomial header costs, charged once per record on the canonical prefix
packet, remain polynomial in the caller's own descriptor scale. -/
theorem rebase (size : X → ℕ) (hs : Dom r.scale size) (d : ℕ) : ∃ e C : ℕ, ∀ i,
    (n i:ℝ)*(w i+(size i+1:ℝ)^d) ≤ (C:ℝ)*mass r n w e i := by
  obtain ⟨e,C,h⟩ := (hs.add (Dom.const _ 1)).pow d
  refine ⟨e,C+1,fun i => ?_⟩
  have h' : (size i+1:ℝ)^d ≤ C*(r.scale i+1:ℝ)^e := by exact_mod_cast h i
  unfold mass
  push_cast
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have pow : 0 ≤ (r.scale i+1:ℝ)^e := by positivity
  nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) C) (Nat.cast_nonneg (α:=ℝ) (w i))]

end Controlled.PrefixCommand

end NearSquareRoot
end Computability
end OAI
