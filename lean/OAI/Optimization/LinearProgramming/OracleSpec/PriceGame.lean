import OAI.Optimization.LinearProgramming.OracleSpec.Machine

/-! Theorem 1.3 of *A strongly polynomial algorithm for linear programming*.
`true` denotes the positive hidden sign and `false` the negative sign. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec

/-- Public input: number of goods, upper bound on integer costs, and zero-based anchor. -/
def priceInput {N : ℕ} (R : ℕ) (anchor : Fin N) : Word :=
  encodeNat N ++ encodeNat R ++ encodeNat anchor.val

/-- One designated zero-based coordinate followed by all `N` rational prices in index order. -/
def priceQuery {N : ℕ} (i : Fin N) (prices : Fin N → ℚ) : Word :=
  encodeNat i.val ++ (List.ofFn prices).flatMap encodeRat

def adjustedCost {N : ℕ} (positive : Bool) (costs : Fin N → ℕ) (prices : Fin N → ℚ)
    (i : Fin N) : ℚ :=
  (costs i : ℚ) + if positive then prices i else -prices i

/-- Only a minimizer on the hidden active set is forced to report the hidden sign. The
quantification is over the actual exchanges, so all other replies may be history-dependent. -/
def priceConsistent {N : ℕ} (positive : Bool) (active : Set (Fin N)) (costs : Fin N → ℕ)
    (history : Transcript) : Prop :=
  ∀ (i : Fin N) (prices : Fin N → ℚ) (answer : Word), (priceQuery i prices, answer) ∈ history →
    i ∈ active → (∀ j ∈ active, adjustedCost positive costs prices i ≤
      adjustedCost positive costs prices j) → answer = [positive]

/-- The algorithm must issue syntactically valid price queries and output a sign regardless of
whether the transcript is consistent with any hidden assignment. -/
def pricePost {N : ℕ} (R : ℕ) (anchor : Fin N) (history : Transcript) (output : Word) : Prop :=
  (∀ exchange ∈ history, ∃ (i : Fin N) (prices : Fin N → ℚ), exchange.1 = priceQuery i prices) ∧
  (∃ b : Bool, output = [b]) ∧
  ∀ (positive : Bool) (active : Set (Fin N)) (costs : Fin N → ℕ), anchor ∈ active →
    (∀ j ∈ active, costs j ≤ R) → priceConsistent positive active costs history →
      output = [positive]

/-- The reference for Theorem 1.3. A single finite program and polynomial are chosen before
all inputs and adaptive one-bit answer strategies. The universal time bound applies even
to inconsistent strategies. Values of `costs` outside `active` enter no comparison. -/
def ExtremalSignRecovery : Prop :=
  ∃ (p : BitProgram) (coefficient degree : ℕ),
    ∀ (N R : ℕ) (_ : 0 < N) (_ : 0 < R) (anchor : Fin N) (reply : Transcript → Word → Bool),
      p.ComputesWithin (fun history query => [reply history query]) (priceInput R anchor)
        (coefficient * (N + (R + 1).log2 + 1) ^ degree) (pricePost R anchor)

end OracleSpec
end LinearProgramming
end Optimization
end OAI
