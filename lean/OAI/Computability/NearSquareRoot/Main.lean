import OAI.Computability.NearSquareRoot.InterchangeROMUniform
import OAI.Computability.NearSquareRoot.SelectedCRTProcedure
import OAI.Computability.NearSquareRoot.SelectedKernelPermutation
import OAI.Computability.NearSquareRoot.SelectedWalshProcedure
import OAI.Computability.NearSquareRoot.UniformWorstCase
import OAI.Computability.IntegerMultiplication.Main

/-! # Uniform integer multiplication with near-square-root logarithmic overhead

A single deterministic finite-alphabet multitape machine multiplies two
unsigned binary strings in most-significant-first order. Its actual worst-case
step count is at most `n * (1 + log n) ^ (1/2 + δ n)` for one `δ` tending to
zero. The visited-space bound counts distinct tape/address pairs through halt.

The rectangular interchanger supplies the forward and backward CRT, Fourier
permutation, and Walsh procedures. The CRT search accepts odd pairwise
coprime axis lengths, including composite lengths. The generated programs
share a register bound. A fixed geometric scheduler runs them in fenced
arenas and copies the successful candidate's product to the output tape.
`uniformMultiplicationSpec_iff_worstCase` takes the maximum over actual
halting traces at each positive width.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open FixedCandidate FixedCandidate.CandidateParameters

/-- All positive excess exponents hold for one physical rule, time function
and visited-space coefficient. The one-degree input guard suffices for the
unary-width CRT tickets in both directions. -/
theorem uniformMultiplication : UniformMultiplicationSpec := by
  obtain ⟨native⟩ := InterchangeROMFamily.exists_native_family
  apply uniform_of_procedures 1
  intro kind
  cases kind with
  | crt d => exact ⟨crtProcedure native 1 (by decide) d⟩
  | permutation d => exact permutationProcedure (selectedFiles native) 1 d
  | walsh d => exact walshProcedure native 1 d

/-- Theorem `thm:uniform-main` with its attained worst-case time and a single
vanishing excess exponent. The output occupies exactly twice the input width. -/
theorem uniformIntegerMultiplication : UniformWorstCaseSpec :=
  uniformMultiplicationSpec_iff_worstCase.mp uniformMultiplication

end NearSquareRoot
end Computability
end OAI
