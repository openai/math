import OAI.Optimization.LinearProgramming.Lattice.OracleQuerySize

/-! A uniform, implementation-independent statement of the sign-query result. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open SignType

theorem rounding_parameter_bounds (p M : ℕ) :
    let B := 100 * (p + M.size + 12) ^ 6
    p * (2*p + 1 + p * searchPrecision p M) ≤ B ∧
      queryCoefficientWidth p M ≤ B ∧ radixWidth p M * p ≤ B := by
  dsimp [searchPrecision, queryCoefficientWidth, radixWidth, precisionExponent]
  refine ⟨?_, ?_, ?_⟩ <;> zify <;> rw [← sub_nonneg] <;> ring_nf <;> positivity

/-- A uniform family of deterministic decision trees recovers all bounded integer
comparisons. The number of actual calls and the magnitude bit lengths of every queried
and returned coordinate are bounded by a single fixed polynomial. -/
theorem signOracleQueryRounding :
    ∃ program : (p M : ℕ) → SignQueries p (Fin p → ℤ), ∀ p M : ℕ, 0 < p → 0 < M →
      let B := 100 * (p + M.size + 12) ^ 6
      (∀ reply, (SignQueries.history reply (program p M)).length ≤ B) ∧
      ∀ (v : Fin p → ℝ) (reply : (Fin p → ℤ) → Bool),
        (∀ c, reply c = true ↔ 0 ≤ dotProduct (fun i => (c i : ℝ)) v) →
        let z := SignQueries.run reply (program p M)
        (∀ c ∈ SignQueries.history reply (program p M), ∀ i, (c i).natAbs.size ≤ B) ∧
        (∀ i, (z i).natAbs.size ≤ B) ∧
        ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
          sign (dotProduct a z) = sign (dotProduct (fun i => (a i : ℝ)) v) := by
  refine ⟨oracleRoundingProgram, ?_⟩
  intro p M hp hM B
  obtain ⟨ht, hq, hz⟩ := rounding_parameter_bounds p M
  constructor
  · intro reply
    rw [SignQueries.history_length]
    exact (roundingProgramWith_cost M _ reply).trans ht
  · intro v reply hOracle z
    have h := roundingProgramWith_correct hp hM _ (search_selector_correct hp hM) v reply hOracle
    refine ⟨?_, fun i => (h.1 i).trans hz, h.2⟩
    intro c hc i
    exact (roundingProgramWith_query_size hp hM _ (search_selector_correct hp hM) v reply hOracle hc i).trans hq

end Lattice
end LinearProgramming
end Optimization
end OAI
