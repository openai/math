import OAI.Optimization.LinearProgramming.PriceGame.ChargingSamplingBand
import OAI.Optimization.LinearProgramming.PriceGame.ChargingTrial

/-! # The two probe tests in Section 6 -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The positive-surplus mass of a probe. -/
def positiveMass (m surplus : V → ℚ) : ℚ := ∑ i ∈ univ.filter (fun j => 0 < surplus j), m i

/-- The fixed normalized tuple distribution used at all probes in a state. -/
def tupleDistribution (m : V → ℚ) (x : Fin 64 → V) : ℚ := drawWeight (fun i => m i / ∑ j, m j) x

/-- Signed gain of an expert, with its outside-option allocation excluded. -/
def probeGain {surplus : V → ℚ} (A : ProbeAllocation 64 surplus) (label : V → ℚ) (x : Fin 64 → V) : ℚ :=
  ∑ i, A.weight x i * label i

omit [DecidableEq V] in
theorem probeGain_lower {m surplus label : V → ℚ} (A : ProbeAllocation 64 surplus)
    (hm : ∀ i, 0 ≤ m i) (hM : 0 < ∑ i, m i) (hl : ∀ i, -1 ≤ label i) :
    -1 ≤ weighted (tupleDistribution m) (probeGain A label) := by
  obtain ⟨hp0, hp1⟩ := active_distribution hm hM
  have hq : ∑ x : Fin 64 → V, tupleDistribution m x = 1 := sum_drawWeight hp1
  calc
    (-1 : ℚ) = ∑ x, tupleDistribution m x * (-1) := by rw [← sum_mul, hq, one_mul]
    _ ≤ weighted (tupleDistribution m) (probeGain A label) := by
      apply sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (drawWeight_nonneg hp0 x)
      apply gain_ge_neg_one label (A.weight x) (A.nonneg x) _ hl
      linarith [A.total x, A.outside_nonneg x]

/-- A supported transition is inherited (`none`) or chooses a positive-surplus
pivot whose strictly higher-surplus vertices fit the duplication budget. -/
def admissibleTest (m surplus : V → ℚ) : Option V → Prop
  | none => positiveMass m surplus ≤ 1/16
  | some j => 0 < surplus j ∧ (∑ i ∈ univ.filter (fun i => surplus j < surplus i), m i) ≤ 1/16

/-- Proof-only selection for testing one shared child call. The distribution is
fixed before choosing a successful pivot. The algorithm observes neither this
selection nor its Boolean classification. -/
structure ProbeTest (m surplus : V → ℚ) (success : Option V → Prop) (G : ℚ) where
  density : Option V → ℚ
  failed : Bool
  nonneg : ∀ j, 0 ≤ density j
  normalized : ∑ j, density j = 1
  cap : ∀ i, density (some i) ≤ 32 * m i
  allowed : ∀ j, 0 < density j → admissibleTest m surplus j
  all_fail : failed = true → ∀ j, 0 < density j → ¬ success j
  pass_gain : failed = false → positiveMass m surplus / 2 ≤ G

/-- Construction of both kinds of probe tests from extremal feedback and an
allocation on actual maximizing choices. The high test calls `high_probe_pivots`
so all its pivots and their admissibility follow from the input masses. -/
theorem exists_probe_test (m surplus label : V → ℚ) (A : ProbeAllocation 64 surplus)
    (hm : ∀ i, 0 ≤ m i) (hM0 : 0 < ∑ i, m i) (hM1 : ∑ i, m i ≤ 1)
    (hlabel : ∀ i, -1 ≤ label i) (success : Option V → Prop)
    (inherit : success none → ∀ i, 0 ≤ surplus i → label i = 1)
    (pivot : ∀ j, success (some j) → ∀ i, surplus j ≤ surplus i → label i = 1) :
    Nonempty (ProbeTest m surplus success (weighted (tupleDistribution m) (probeGain A label))) := by
  classical
  by_cases hlow : positiveMass m surplus ≤ 1/16
  · refine ⟨{ density := fun j => if j = none then 1 else 0
              failed := decide (¬success none)
              nonneg := fun j => by split <;> norm_num
              normalized := by simp
              cap := fun i => by simp [hm i]
              allowed := ?_, all_fail := ?_, pass_gain := ?_ }⟩
    · intro j hj
      cases j with
      | none => exact hlow
      | some i => simp at hj
    · intro hf j hj
      cases j with
      | none => simpa using hf
      | some i => simp at hj
    · intro hf
      have hw : success none := by simpa using hf
      exact passing_probe_expected_gain m surplus label A hm hM0 hM1 hlabel
        (univ.filter (fun i => 0 < surplus i)) (by simp) (fun _ => inherit hw)
        (fun hh => (not_lt_of_ge hlow hh).elim)
  · have hlarge := lt_of_not_ge hlow
    obtain ⟨p, htotal, hbound, hvalid, hpass⟩ := high_probe_pivots m surplus label A hm hM0 hM1
      hlabel hlarge (fun j => success (some j)) pivot
    let good : Prop := ∃ j, 0 < p j ∧ success (some j)
    let μ : Option V → ℚ := fun j => j.elim 0 p
    refine ⟨{ density := μ, failed := decide (¬good),
              nonneg := ?_, normalized := ?_, cap := ?_, allowed := ?_, all_fail := ?_, pass_gain := ?_ }⟩
    · rintro (_ | j)
      · exact le_rfl
      · exact (hbound j).1
    · simpa [μ, Fintype.sum_option] using htotal
    · intro i
      change p i ≤ 32 * m i
      convert (hbound i).2 using 1; ring
    · rintro (_ | j) hj
      · exact (lt_irrefl 0 hj).elim
      · exact ⟨(hvalid j hj).1, (hvalid j hj).2.le⟩
    · intro hf
      have hn : ¬good := by simpa using hf
      rintro (_ | j) hj hs
      · exact (lt_irrefl 0 hj).elim
      · exact hn ⟨j, hj, hs⟩
    · intro hf
      have hg : good := by simpa using hf
      have hv : positiveMass m surplus ≤ 1 :=
        (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hm i)).trans hM1
      have hhalf : positiveMass m surplus / 2 ≤ 1/2 := by linarith
      exact hhalf.trans (hpass hg)

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI
