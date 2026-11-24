import OAI.Computability.VPVNP.AdviceCircuitCompiler
import OAI.Computability.VPVNP.UniversalCountStackBounds
import OAI.Computability.VPVNP.VerifierMachine

/-!
# The circuit advice for the integer coefficient of the paired family

The same advice program verifies every input and candidate path of a given
length. It simulates the decoded machine on the full input, including its own
prefix, using the canonical zero-padded choices. The deterministic enumeration
thus computes the integer coefficient before reduction into any field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalCountStack

open RAMTape TapeWord VerifierMachine

/-- The gate instructions for checking a canonical path of the universal machine on an input of
length n, shared by every input and candidate path of that length. -/
noncomputable def verifierProgram (n : ℕ) := AdviceCircuit.compile (verifierCircuit n)

theorem verifierProgram_run {n : ℕ} (x : Fin n → Bool) (bits : Fin (n^clockExponent) → Bool) :
    ∃ tail, AdviceCircuit.run (verifierProgram n) (AdviceCircuit.inputs x bits) =
      some (verifiesInput x bits :: tail) := by
  simpa only [verifierProgram, verifierCircuit_eval] using
    AdviceCircuit.compile_run (verifierCircuit n) x bits

theorem verifierProgram_advice_polynomial :
    PolynomiallyBounded (fun n => (AdviceCircuit.encode (verifierProgram n)).length) := by
  have hs := verifierSize_polynomiallyBounded
  have hsum := (((hs.add .id).add (PolynomiallyBounded.id.pow clockExponent)).add (.const 2))
  exact ((hs.add (.const 2)).mul (((PolynomiallyBounded.const 2).mul hsum).add (.const 3))).of_le
    (fun n => AdviceCircuit.compile_size (verifierCircuit n))

/-- The raw integer count fits even when every path branches and accepts. -/
theorem acceptingCount_le {n : ℕ} (x : Fin n → Bool) : acceptingCount x ≤ 2^(n^clockExponent) := by
  rw [acceptingCount_eq_card_witnesses]
  simpa using Finset.card_le_card (Finset.filter_subset _ (Finset.univ : Finset (Fin (n^clockExponent) → Bool)))

/-- Reading the final stack as a natural number retains the entire path count. -/
theorem count_digits_value {n : ℕ} (x : Fin n → Bool) :
    value (digits (n^clockExponent + 1) (acceptingCount x)) = acceptingCount x := by
  rw [value_digits, Nat.mod_eq_of_lt]
  have := acceptingCount_le x
  rw [pow_succ]
  have : 0 < 2^(n^clockExponent) := pow_pos (by decide) _
  omega

end UniversalCountStack

end VPVNP
end Computability
end OAI
