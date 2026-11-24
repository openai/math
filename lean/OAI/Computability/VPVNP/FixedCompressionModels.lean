import OAI.Computability.VPVNP.IteratedCompression
import OAI.Computability.VPVNP.CompressorEvaluatorAdvice

/-!
# One compressor and its specializations at small-circuit lengths

Sections 8 and 9 use the same compression schedule and the same integer
parameter equations at every length of the contradiction. Only the grammar
assignment and the finite algebra realizing both assignments are selected
at an individual small-circuit length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open MvPolynomial LabelEvaluator

/-- The fixed field solution and both templates precede the universal
quantifier over small-circuit lengths. At each such length one finite
algebra realizes the grammar and both kinds of wire maps together. The
prime in positive characteristic is the original characteristic. -/
theorem fixed_models_of_small_circuits (k : Type*) [Field k] (q : ℕ) [CharP k q]
    {C : ℕ} (hC : 1 ≤ C)
    (hsmall : ∀ N, ∃ n ≥ N, circuitSize (map (Int.castRingHom k) (P n)) ≤ n ^ C) :
    ∃ (S : BlockSchedule k) (B : S.Templates),
      (∃ κ : B.Entry → k, B.IsSolution κ) ∧
      ∀ n (hn : 2 ≤ n), circuitSize (map (Int.castRingHom k) (P n)) ≤ n ^ C →
        ∃ p : Nat.Primes, (q ≠ 0 → p.val = q) ∧ (q = 0 → p.val ≤ 2 ^ B.compressorPrimeBits C n) ∧
          Nonempty (Model p (B.compressorDegree n) (B.compressorEquations hn C)) := by
  obtain ⟨S, B, κ, hκ⟩ := fixed_templates_of_small_circuits k hC hsmall
  refine ⟨S, B, ⟨κ, hκ⟩, fun n hn hsize => ?_⟩
  obtain ⟨s, hs, circ, hcirc⟩ := circuitSize_le_iff.mp hsize
  exact B.exists_compressorEvaluator q hn hC hs circ hcirc

end Compression

end VPVNP
end Computability
end OAI
