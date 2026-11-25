import OAI.LinearAlgebra.MatrixExponent.Integral.RingFormula
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Consequences
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Randomness
import OAI.LinearAlgebra.MatrixExponent.Rounds.Compression
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.LocalSort
import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Local
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.ReaderInputs
import OAI.LinearAlgebra.SpectralBooks.ExactExponent

/-!
# Matrix multiplication exponents

`OAI.LinearAlgebra.SpectralBooks.square_exponent` gives the value `9 / 4` for
division-free circuits over every field. For just that theorem, import
`OAI.LinearAlgebra.SpectralBooks.ExactExponent`.

The proof identifies the two circuit models by finite tensor rank. Over prime
fields, `BatchDescent.hard` and `Rounds.installable` rule out simultaneous
spectral prices. This gives square equality and rectangular rigidity together.

* `omega_eq` computes the square exponent for rational circuits.
* `Rectangle.exponent_eq` gives the formula for nonnegative rectangular shapes.
* `Integral.exponent_eq` extends the division-free formula to nonzero commutative rings.

The reductions below give equivalent rank bounds and sufficient network estimates.
-/

namespace OAI.LinearAlgebra.MatrixExponent

/-- The obstruction can be checked entirely on finite rank decompositions. -/
theorem square_of_prime_ranks
    (h : ∀ (p : ℕ) [Fact p.Prime] (n r : ℕ), 2 ≤ n →
      RankLE (ZMod p) n r → n ^ 9 ≤ r ^ 4)
    (F : Type*) [Field F] : omega F = 9 / 4 := by
  refine le_antisymm (upper_bound F) (le_of_not_gt ?_)
  intro bad
  obtain ⟨p, _, hp⟩ := prime_specialization bad
  obtain ⟨n, r, hn, hr, hs⟩ := omega_lt_iff_rank.mp hp
  exact (h p n r hn hr).not_gt ((rank_threshold n r).mp hs)

/-- The same integer lower bound is necessary. -/
theorem square_iff_prime_ranks :
    (∀ (F : Type) [Field F], omega F = 9 / 4) ↔
      ∀ (p : ℕ) [Fact p.Prime] (n r : ℕ), 2 ≤ n →
        RankLE (ZMod p) n r → n ^ 9 ≤ r ^ 4 := by
  constructor
  · intro h p _ n r hn hr
    by_contra! bad
    exact (h (ZMod p)).ge.not_gt (omega_lt_of_rank hn hr ((rank_threshold n r).mpr bad))
  · exact fun h F _ => square_of_prime_ranks h F

/-- Many-list hardness and compression over prime fields suffice for square equality. -/
theorem square_of_network_bounds
    (lower : ∀ (p : ℕ) [Fact p.Prime], ManyList (Realizes (ZMod p)))
    (compress : ∀ (p : ℕ) [Fact p.Prime],
      omega (ZMod p) < 9 / 4 → Compression (Realizes (ZMod p)))
    (F : Type*) [Field F] : omega F = 9 / 4 := by
  refine le_antisymm (upper_bound F) (le_of_not_gt ?_)
  intro bad
  obtain ⟨p, _, hp⟩ := prime_specialization bad
  exact incompatible (seed (ZMod p)) (lower p) (compress p hp)

/-- The two uses of tagged permutations have different exponents. A fixed
positive overhead suffices for hardness. An exponent strictly below two
suffices for lookup. -/
theorem square_of_tag_and_arity
    (hard : ∀ (p : ℕ) [Fact p.Prime], Tagged.Hard (ZMod p))
    (saving : ∀ (p : ℕ) [Fact p.Prime], omega (ZMod p) < 9 / 4 →
      (∃ q : ℝ, 1 < q ∧ q < 2 ∧ Lookup.ShortTag (ZMod p) q) ∧ ArityReduction (ZMod p))
    (F : Type*) [Field F] : omega F = 9 / 4 := by
  apply square_of_network_bounds (fun p _ => Tagged.manyList_of_tag (hard p)) _ F
  intro p _ hp
  obtain ⟨⟨q, hq, hq', tag⟩, stage⟩ := saving p hp
  exact (compresses_of_stages hq hq' (Lookup.sorting_of_tag hq.le tag) stage).lists

end OAI.LinearAlgebra.MatrixExponent
