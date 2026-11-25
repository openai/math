import OAI.Optimization.LinearProgramming.PriceGame.ChargingFeedback
import OAI.Optimization.LinearProgramming.PriceGame.ChargingProbe

/-! # The test of a probe with its actual inherited and pivot child states -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging

open Finset States

variable {V I : Type*}

/-- A correct Boolean feedback label has signed gain one; a disagreement has gain minus one. -/
def labelAgreement (h b : Bool) : ℚ := if b = h then 1 else -1

theorem labelAgreement_lower (h b : Bool) : -1 ≤ labelAgreement h b := by
  simp only [labelAgreement]; split <;> norm_num

/-- The inherited or pivot shift, on a finite list of active vertices inside the ambient
price space. The returned child price vector is shared across all choices. -/
def trialShift (vertex : V → I) (P y : I → ℚ) (h : Bool) (t : ℚ) : Option V → ℚ
  | none => t
  | some k => pivotShift P y h (vertex k)

/-- The test requires both a legal increase of the shift and the success of the returned
price vector in the indicated child state. On every supported pivot the increase is strict. -/
def actualSuccess (vertex : V → I) (S : I → Prop) (P y : I → ℚ) (h : Bool)
    (t : ℚ) (x : I × Bool → ℚ) (j : Option V) : Prop :=
  t ≤ trialShift vertex P y h t j ∧ childPass S P y h (trialShift vertex P y h t j) x

/-- The two definitions of violated mass in the trial coincide after expressing the
threshold in the original price coordinates. -/
theorem positiveMass_eq_violatedMass [Fintype V] (vertex : V → I) (m : V → ℚ)
    (P y : I → ℚ) (h : Bool) (t : ℚ) :
    positiveMass m (fun v => probeSurplus P y h t (vertex v)) =
      violatedMass m h (fun v => signed h (P (vertex v) - t)) (fun v => y (vertex v)) := by
  classical
  rw [positiveMass, sum_filter, violatedMass, weighted]
  apply sum_congr rfl
  intro v _
  have eq := misses_iff_positive_surplus P y h t (vertex v)
  by_cases hit : 0 < probeSurplus P y h t (vertex v)
  · simp [hit, eq.mpr hit]
  · have hm : misses h (signed h (P (vertex v) - t)) (y (vertex v)) = false := by
      cases hm : misses h (signed h (P (vertex v) - t)) (y (vertex v)) with
      | false => rfl
      | true => exact (hit (eq.mp hm)).elim
    simp [hit, hm]

/-- Build the test from the actual shared child prices, baseline, designated tie replies,
and allocations maximizing corrected comparisons. The parameters `vertex` and `live`
let the tuple distribution range over just the active type. -/
theorem actual_probe_test [Fintype V] [DecidableEq V] (vertex : V → I) {S : I → Prop}
    (live : ∀ v, S (vertex v)) (m : V → ℚ) (P y : I → ℚ) (h : Bool) (t : ℚ)
    (x : I × Bool → ℚ) (answer : I → Bool)
    (valid : ∀ i, y i = parentPrices y x i → Extreme S P (parentPrices y x) h t i → answer i = h)
    (A : ProbeAllocation 64 (fun v => probeSurplus P y h t (vertex v)))
    (hm : ∀ v, 0 ≤ m v) (hM0 : 0 < ∑ v, m v) (hM1 : ∑ v, m v ≤ 1) :
    Nonempty (ProbeTest m (fun v => probeSurplus P y h t (vertex v))
      (actualSuccess vertex S P y h t x) (weighted (tupleDistribution m)
        (probeGain A (fun v => labelAgreement h (probeFeedback y x answer (vertex v)))))) := by
  apply exists_probe_test m _ _ A hm hM0 hM1 (fun _ => labelAgreement_lower _ _) _
  · intro hs v hv
    have win := (inherited_feedback hs.2 valid).2 (vertex v) (live v) hv
    simp [labelAgreement, win]
  · intro k hs v hv
    have hshift : t ≤ pivotShift P y h (vertex k) := hs.1
    have hk : 0 ≤ probeSurplus P y h t (vertex k) := by
      dsimp only [pivotShift, probeSurplus] at *
      linarith
    have win := (pivot_feedback hk hs.2 valid).2 (vertex v) (live v) hv
    simp [labelAgreement, win]

/-- Supported transitions advance the shift, so a failed test certifies failure of
the actual child prices for each transition of positive probability. -/
theorem failed_actual_child [Fintype V] [DecidableEq V] {vertex : V → I} {S : I → Prop}
    {m : V → ℚ} {P y : I → ℚ} {h : Bool} {t G : ℚ} {x : I × Bool → ℚ}
    (test : ProbeTest m (fun v => probeSurplus P y h t (vertex v))
      (actualSuccess vertex S P y h t x) G)
    (failed : test.failed = true) {j : Option V} (hp : 0 < test.density j) :
    ¬ childPass S P y h (trialShift vertex P y h t j) x := by
  intro win
  apply test.all_fail failed j hp
  refine ⟨?_, win⟩
  cases j with
  | none => exact le_rfl
  | some v =>
    have hs : 0 < probeSurplus P y h t (vertex v) := (test.allowed (some v) hp).1
    dsimp only [probeSurplus, trialShift, pivotShift] at hs ⊢
    linarith

/-- When the finite type indexes the active parent vertices, every supported test state
really fits the child duplication budget. This uses the weights of its cheap and expensive
copies, with strict surplus ties counted only once. -/
theorem supported_child_mass [Fintype V] [DecidableEq V] {m P y : V → ℚ}
    {h : Bool} {t G : ℚ} {success : Option V → Prop}
    (test : ProbeTest m (probeSurplus P y h t) success G)
    (hM : ∑ i, m i ≤ 1) {j : Option V} (hp : 0 < test.density j) :
    ∑ q ∈ Mass.childActive h univ
      (Mass.violators univ (fun i => P i - signed h (y i)) (trialShift id P y h t j)),
        Mass.factor h q.2 * m q.1 ≤ 1 := by
  apply Mass.transition_admissible m h univ _ _ hM
  have ha := test.allowed j hp
  cases j with
  | none =>
    change ∑ i ∈ univ.filter (fun i => t < P i - signed h (y i)), m i ≤ 1/16
    change positiveMass m (probeSurplus P y h t) ≤ 1/16 at ha
    have same : (univ.filter fun i => t < P i - signed h (y i)) =
        univ.filter (fun i => 0 < probeSurplus P y h t i) := by
      apply filter_congr
      intro i _
      change (t < P i - States.signed h (y i)) ↔ 0 < P i - t - States.signed h (y i)
      constructor <;> intro hlt <;> linarith
    rw [same]
    exact ha
  | some v =>
    change ∑ i ∈ univ.filter (fun i => P v - signed h (y v) < P i - signed h (y i)), m i ≤ 1/16
    have same : (univ.filter fun i => P v - signed h (y v) < P i - signed h (y i)) =
        univ.filter (fun i => probeSurplus P y h t v < probeSurplus P y h t i) := by
      apply filter_congr
      intro i _
      change (P v - States.signed h (y v) < P i - States.signed h (y i)) ↔
        P v - t - States.signed h (y v) < P i - t - States.signed h (y i)
      constructor <;> intro hlt <;> linarith
    rw [same]
    exact ha.2

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI
