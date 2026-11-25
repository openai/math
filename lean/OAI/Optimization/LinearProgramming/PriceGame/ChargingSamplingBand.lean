import OAI.Optimization.LinearProgramming.PriceGame.ChargingQuantile
import OAI.Optimization.LinearProgramming.PriceGame.ChargingSampling

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging

/-- For a high-surplus probe, choose the pivot distribution before checking any successor.
Every pivot of positive probability is admissible. Success at any such pivot makes the
common upper band correctly labelled and forces the expected gain to be at least 1/2. -/
theorem high_probe_pivots {V : Type*} [Fintype V] [DecidableEq V]
    (m surplus label : V → ℚ) (A : ProbeAllocation 64 surplus) (hm : ∀ i, 0 ≤ m i)
    (hm₀ : 0 < ∑ i, m i) (hm₁ : ∑ i, m i ≤ 1) (hsign : ∀ i, -1 ≤ label i)
    (large : 1 / 16 < ∑ i ∈ Finset.univ.filter (fun i => 0 < surplus i), m i)
    (succeeds : V → Prop)
    (feedback : ∀ v, succeeds v → ∀ i, surplus v ≤ surplus i → label i = 1) :
    ∃ p : V → ℚ, (∑ i, p i) = 1 ∧
      (∀ i, 0 ≤ p i ∧ p i ≤ 2 * m i / (1 / 16)) ∧
      (∀ i, 0 < p i → 0 < surplus i ∧
        (∑ j ∈ Finset.univ.filter (fun j => surplus i < surplus j), m j) < 1 / 16) ∧
      ((∃ i, 0 < p i ∧ succeeds i) →
        1 / 2 ≤ ∑ x : Fin 64 → V, drawWeight (fun i => m i / ∑ j, m j) x *
          ∑ i, A.weight x i * label i) := by
  obtain ⟨p, band, hp, hcap, hmass, hpos, habove⟩ :=
    positive_surplus_pivots m surplus hm (by norm_num : (0 : ℚ) < 1 / 16) large.le
  refine ⟨p, hp, hcap, fun i hi => ⟨(habove i hi).1, (habove i hi).2.1⟩, ?_⟩
  rintro ⟨v, hv, hwin⟩
  let prob (i : V) := m i / ∑ j, m j
  let gain (x : Fin 64 → V) := ∑ i, A.weight x i * label i
  have ⟨hprob₀, hprob⟩ := active_distribution hm hm₀
  have hband : 1 / 32 ≤ ∑ i ∈ band, prob i := by
    have hraw : 1 / 32 ≤ ∑ i ∈ band, m i := by linarith
    exact hraw.trans (active_subset_mass hm hm₀ hm₁ band)
  have wins : ∀ x : Fin 64 → V, (∃ j, x j ∈ band) → 1 ≤ gain x := by
    rintro x ⟨j, hj⟩
    exact (gain_eq_one_of_pivot_hit x surplus label (A.weight x) (A.outside x) (surplus v)
      (A.nonneg x) (A.outside_nonneg x) (A.total x) (A.outside_max x) (A.inside_max x)
      (fun i _ hi => feedback v hwin i hi)
      ⟨j, (habove v hv).2.2 (x j) hj, hpos (x j) hj⟩).ge
  have bounds : ∀ x, -1 ≤ gain x := by
    intro x
    apply gain_ge_neg_one label (A.weight x) (A.nonneg x) _ hsign
    linarith [A.total x, A.outside_nonneg x]
  exact high_surplus_expected_gain prob hprob₀ hprob band hband gain wins bounds

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI
