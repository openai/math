import OAI.Hierarchy.ProbeLedger

namespace OAI
/-! # Uniform stopping for the adaptive mesh with a signed cash account

An early exit pays the crude remaining cost.  The code uses the same fixed
fuel in every selector branch, and permits a cash account arbitrarily far
below zero. -/

namespace Hierarchy.AdaptiveProbe
noncomputable section

private def stopped {X : Type*} (good : X → Bool) (price : X → ℝ) (floor : ℝ) (x : X) : Bool :=
  good x || decide (price x ≤ floor)

/-- Run at most the allotted number of real repair passes. Each step sees the
state left by the preceding histogram selection. -/
def repair {X : Type*} (step : ℕ → X → X) (good : X → Bool) (price : X → ℝ) (floor : ℝ)
    (x : X) : ℕ → X
  | 0 => x
  | j+1 => let y := repair step good price floor x j
           if stopped good price floor y then y else step j y

private theorem stopped_iff {X : Type*} (good : X → Bool) (price : X → ℝ) (floor : ℝ) (x : X) :
    stopped good price floor x=true ↔ good x=true ∨ price x ≤ floor := by simp [stopped]

/-- The concrete bounded pass either reaches low excess or already saves enough
for the remaining work. No lower bound on the signed ledger is required. -/
theorem repair_receipt {X : Type*} (step : ℕ → X → X) (good : X → Bool) (price : X → ℝ)
    (floor gain : ℝ) (hg : 0 < gain) (x : X) (fuel : ℕ)
    (enough : price x - (fuel:ℝ)*gain ≤ floor)
    (saving : ∀ j < fuel, ∀ y, good y=false → floor < price y → price (step j y)+gain ≤ price y) :
    let y := repair step good price floor x fuel
    price y ≤ price x ∧ (good y=true ∨ price y ≤ floor) := by
  let Y := repair step good price floor x
  have h (j : ℕ) (hj : j ≤ fuel) : price (Y j) ≤ price x ∧
      (stopped good price floor (Y j)=true ∨ price (Y j)+(j:ℝ)*gain ≤ price x) := by
    induction j with
    | zero => exact ⟨le_rfl,Or.inr (by simp [Y,repair])⟩
    | succ j ih =>
      obtain ⟨mon,progress⟩ := ih (by omega)
      by_cases halt : stopped good price floor (Y j)=true
      · have eq : Y (j+1)=Y j := by simp only [Y,repair,ite_eq_left halt]
        rw [eq]
        exact ⟨mon,Or.inl halt⟩
      · have eq : Y (j+1)=step j (Y j) := by simp only [Y,repair,ite_eq_right halt]
        have cont := mt (stopped_iff good price floor (Y j)).2 halt
        have d := saving j (by omega) (Y j) (by simpa using (not_or.mp cont).1)
          (lt_of_not_ge (not_or.mp cont).2)
        rw [eq,Nat.cast_succ,add_mul,one_mul]
        exact ⟨by linarith,Or.inr (by linarith [progress.resolve_left halt])⟩
  obtain ⟨mon,done|saved⟩ := h fuel le_rfl
  · exact ⟨mon,(stopped_iff ..).mp done⟩
  · exact ⟨mon,Or.inr (by linarith)⟩

/-- The physical program can take one integer fuel bound for all sufficiently
large sizes and all trajectories whose entry price respects the uniform bound. -/
theorem exists_repair_fuel {upper floor gain : ℝ} (hg : 0 < gain) :
    ∃ fuel : ℕ, ∀ x : ℝ, x ≤ upper → x-fuel*gain ≤ floor := by
  obtain ⟨fuel,h⟩ := exists_nat_gt ((upper-floor)/gain)
  refine ⟨fuel,?_⟩
  have h' := (div_lt_iff₀ hg).mp h
  intro x small
  linarith

end
end Hierarchy.AdaptiveProbe

end OAI
