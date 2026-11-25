import OAI.Optimization.LinearProgramming.Lattice.ShortSelector
import OAI.Optimization.LinearProgramming.Lattice.Rational
import OAI.Optimization.LinearProgramming.Lattice.OracleQuerySize

/-! Sign-preserving rounding using native rational LLL on the graph lattice. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open SignType

/-- The sign-only computation of Appendix A with deterministic rational LLL selecting
the integer approximation at every residual step. -/
def lllRoundingProgram (p M : ℕ) : SignQueries p (Fin p → ℤ) :=
  roundingProgramWith M (lllShortSelector M)

/-- Correctness and bounds on all oracle communication and returned coordinates for the
actual LLL-backed rounding algorithm. -/
theorem lllRoundingProgram_correct {p M : ℕ} (hp : 0 < p) (hM : 0 < M)
    (v : Fin p → ℝ) (oracle : (Fin p → ℤ) → SignType)
    (hOracle : ∀ c, oracle c = sign (dotProduct (realCoordinates c) v)) :
    let reply := fun c => decide (0 ≤ oracle c)
    let z := SignQueries.run reply (lllRoundingProgram p M)
    SignQueries.cost reply (lllRoundingProgram p M) ≤ p * (2 * p + 1 + p * searchPrecision p M) ∧
    (∀ c ∈ SignQueries.history reply (lllRoundingProgram p M), ∀ i,
      (c i).natAbs.size ≤ queryCoefficientWidth p M) ∧
    (∀ i, (z i).natAbs.size ≤ radixWidth p M * p) ∧
    ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
      sign (dotProduct a z) = sign (dotProduct (realCoordinates a) v) := by
  intro reply z
  have hr (c) : reply c = true ↔ 0 ≤ formValue c v := by
    simp only [reply, decide_eq_true_eq, hOracle, sign_nonneg_iff]
    rfl
  exact ⟨roundingProgramWith_cost M _ reply,
    fun _ hc i => roundingProgramWith_query_size hp hM _ (lllShortSelector_correct hp hM) v reply hr hc i,
    roundingProgramWith_correct hp hM _ (lllShortSelector_correct hp hM) v reply hr⟩

/-- Round a rational input using only arithmetic comparisons against the original rewards. -/
def roundRationalWithLLL {p : ℕ} (M : ℕ) (v : Fin p → ℚ) : Fin p → ℤ :=
  SignQueries.run (fun c => decide (0 ≤ rationalSignOracle v c)) (lllRoundingProgram p M)

theorem roundRationalWithLLL_correct {p M : ℕ} (hp : 0 < p) (hM : 0 < M) (v : Fin p → ℚ) :
    (∀ i, (roundRationalWithLLL M v i).natAbs.size ≤ radixWidth p M * p) ∧
      ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
        sign (dotProduct a (roundRationalWithLLL M v)) = sign (dotProduct (fun i => (a i : ℚ)) v) := by
  have h := lllRoundingProgram_correct hp hM (fun i => (v i : ℝ)) (rationalSignOracle v)
    (rationalSignOracle_correct v)
  exact ⟨h.2.2.1, fun a ha => (h.2.2.2 a ha).trans (rationalSignOracle_correct v a).symm⟩

end Lattice
end LinearProgramming
end Optimization
end OAI
