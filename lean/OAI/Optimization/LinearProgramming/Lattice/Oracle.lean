import OAI.Optimization.LinearProgramming.Lattice.Selection
import OAI.Optimization.LinearProgramming.Lattice.QueryTree
import OAI.Optimization.LinearProgramming.Lattice.ProjectionTable

/-! A sign-only program producing a bounded comparison vector. Its free-query-tree cost
counts each actual sign request; the rational approximation selector runs between queries. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open SignType WithLp

variable {p : ℕ}

/-- Collect ordered digit vectors through rational residual probes. -/
def directionsQ (M : ℕ) (select : (Fin p → ℚ) → ℕ × (Fin p → ℤ)) :
    ℕ → List (Fin p → ℤ) → SignQueries p (List (Fin p → ℤ))
  | 0, _ => .done []
  | fuel + 1, old =>
    (probeRowsQ (residualTableMatrix old) (searchPrecision p M)).bind fun reply =>
      match reply with
      | none => .done []
      | some u =>
        let z := (select u).2
        (directionsQ M select fuel (z :: old)).bind fun zs => .done (z :: zs)

theorem run_directionsQ (M : ℕ) (select : (Fin p → ℚ) → ℕ × (Fin p → ℤ))
    (oracle : (Fin p → ℤ) → Bool) (fuel : ℕ) (old : List (Fin p → ℤ)) :
    SignQueries.run oracle (directionsQ M select fuel old) =
      directionLoop (selectedDirection (fun zs =>
        SignQueries.run oracle (probeRowsQ (rationalResidualMatrix zs) (searchPrecision p M))) select) fuel old := by
  induction fuel generalizing old with
  | zero => rfl
  | succ fuel ih =>
    simp only [directionsQ, residualTableMatrix_eq, SignQueries.run_bind, directionLoop, selectedDirection]
    cases h : SignQueries.run oracle (probeRowsQ (rationalResidualMatrix old) (searchPrecision p M)) with
    | none => rfl
    | some u => simp only [Option.map_some, SignQueries.run_bind, SignQueries.run, ih]

theorem cost_directionsQ (M : ℕ) (select : (Fin p → ℚ) → ℕ × (Fin p → ℤ))
    (oracle : (Fin p → ℤ) → Bool) (fuel : ℕ) (old : List (Fin p → ℤ)) :
    SignQueries.cost oracle (directionsQ M select fuel old) ≤ fuel * (2 * p + 1 + p * searchPrecision p M) := by
  induction fuel generalizing old with
  | zero => simp [directionsQ, SignQueries.cost]
  | succ fuel ih =>
    rw [directionsQ, residualTableMatrix_eq, SignQueries.cost_bind, Nat.succ_mul]
    have hb := probeRowsQ_cost oracle (rationalResidualMatrix old) (searchPrecision p M)
    cases h : SignQueries.run oracle (probeRowsQ (rationalResidualMatrix old) (searchPrecision p M)) with
    | none => simp [SignQueries.cost]; omega
    | some u =>
      simp only [SignQueries.cost_bind, SignQueries.cost, Nat.add_zero]
      have ht := ih ((select u).2 :: old)
      omega

/-- The oracle program with a supplied finite rational-arithmetic selector. -/
def roundingProgramWith (M : ℕ) (select : (Fin p → ℚ) → ℕ × (Fin p → ℤ)) :
    SignQueries p (Fin p → ℤ) :=
  (directionsQ M select p []).bind fun zs => .done (radixVector ((2 : ℤ) ^ radixWidth p M) zs)

/-- Uniform upper bound on sign requests for every reply function. -/
theorem roundingProgramWith_cost (M : ℕ) (select : (Fin p → ℚ) → ℕ × (Fin p → ℤ))
    (oracle : (Fin p → ℤ) → Bool) :
    SignQueries.cost oracle (roundingProgramWith M select) ≤ p * (2 * p + 1 + p * searchPrecision p M) := by
  simpa only [roundingProgramWith, SignQueries.cost_bind, SignQueries.cost, Nat.add_zero] using
    cost_directionsQ M select oracle p []

theorem residualProbe_correct {M : ℕ} (v : Fin p → ℝ) (oracle : (Fin p → ℤ) → Bool)
    (hOracle : ∀ c, oracle c = true ↔ 0 ≤ formValue c v) (old : List (Fin p → ℤ)) :
    let P := rationalResidualMatrix old
    let S := integerDirectionSpan old
    let probe := SignQueries.run oracle (probeRowsQ P (searchPrecision p M))
    (probe = none ↔ toLp 2 v ∈ S) ∧ ∀ u, probe = some u → ∀ i,
      |roundingDirection S v i - (u i : ℝ)| ≤ 1 / (2 : ℝ) ^ searchPrecision p M := by
  intro P S probe
  have he : (fun i => ∑ j, (P i j : ℝ) * v j) = (residual S v).ofLp :=
    congrArg WithLp.ofLp (rationalResidualMatrix_correct old v)
  constructor
  · rw [← residual_eq_zero_iff, show probe = none ↔ _ from probeRowsQ_none_iff oracle v hOracle P _]
    constructor
    · intro hz
      ext i
      exact (congrFun he i).symm.trans (hz i)
    · intro hz i
      exact (congrFun he i).trans (by simp [hz])
  · intro u hu i
    obtain rfl := probeRowsQ_some oracle P (searchPrecision p M) hu
    have hh := normalizedRowApprox_error oracle v hOracle P (searchPrecision p M) i
    rw [he] at hh
    exact hh

theorem roundingProgramWith_correct {M : ℕ} (hp : 0 < p) (hM : 0 < M)
    (select : (Fin p → ℚ) → ℕ × (Fin p → ℤ))
    (hsel : ∀ u, 0 < (select u).1 ∧ (select u).1 ≤ searchDenominator p M ^ (p + 1) ∧
      ∀ i, |((select u).1 : ℚ) * u i - (select u).2 i| ≤ 1 / (8 * (p : ℚ) * M))
    (v : Fin p → ℝ) (oracle : (Fin p → ℤ) → Bool)
    (hOracle : ∀ c, oracle c = true ↔ 0 ≤ formValue c v) :
    let z := SignQueries.run oracle (roundingProgramWith M select)
    (∀ i, (z i).natAbs.size ≤ radixWidth p M * p) ∧
      ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
        sign (dotProduct a z) = sign (dotProduct (realCoordinates a) v) := by
  simp only [roundingProgramWith, SignQueries.run_bind, SignQueries.run, run_directionsQ]
  apply roundWithSelection_correct hp hM v _ select
  · exact fun old => (residualProbe_correct (M := M) v oracle hOracle old).1
  · exact fun old => (residualProbe_correct (M := M) v oracle hOracle old).2
  · exact hsel

/-- A fully determined sign-only computation, using exhaustive rational approximation.
The queried vectors and the returned vector use integer coordinates. -/
def oracleRoundingProgram (p M : ℕ) : SignQueries p (Fin p → ℤ) :=
  roundingProgramWith M (rationalDirichlet (searchDenominator p M))

/-- Given signs as in Appendix A, this program preserves ties and all bounded comparisons.
The free interaction tree counts queries; the output bound uses the bit lengths of
`M` and each signed integer coordinate's absolute value. -/
theorem oracleRoundingProgram_correct {M : ℕ} (hp : 0 < p) (hM : 0 < M)
    (v : Fin p → ℝ) (oracle : (Fin p → ℤ) → SignType)
    (hOracle : ∀ c, oracle c = sign (dotProduct (realCoordinates c) v)) :
    let reply := fun c => decide (0 ≤ oracle c)
    let z := SignQueries.run reply (oracleRoundingProgram p M)
    SignQueries.cost reply (oracleRoundingProgram p M) ≤ p * (2 * p + 1 + p * searchPrecision p M) ∧
    (∀ i, (z i).natAbs.size ≤ radixWidth p M * p) ∧
      ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
        sign (dotProduct a z) = sign (dotProduct (realCoordinates a) v) := by
  intro reply z
  refine ⟨roundingProgramWith_cost _ _ _, roundingProgramWith_correct hp hM _
    (search_selector_correct hp hM) v reply ?_⟩
  intro c
  simp only [reply, decide_eq_true_eq, hOracle, sign_nonneg_iff]
  rfl

end Lattice
end LinearProgramming
end Optimization
end OAI
