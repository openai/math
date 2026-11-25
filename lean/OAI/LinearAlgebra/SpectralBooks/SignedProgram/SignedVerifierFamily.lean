import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedVerifierAssembly
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedVerifierBudget
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramGuessWidth

/-! # Assembling polynomial-size families of clocked signed verifiers -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram
open ExactQuantumFactoring Filter

/-- Polynomial bounds for parsing and a single local tick suffice for the
full verifier. The tick estimate is used only inside the actual clock. -/
theorem polynomialSignedVerifier_of_fullVerifier
    (accept : (n : ℕ) → BooleanNetwork (n+Hot.decodeGuessWidth n) 1)
    (step : (n r : ℕ) → BooleanNetwork ((n+Hot.decodeGuessWidth n+1)+frameWidth n (r+1)) (frameWidth n r))
    {P a C b : ℕ}
    (haccept : ∀ᶠ n : ℕ in atTop, (accept n).net.count ≤ P*(n+2)^a)
    (hstep : ∀ᶠ n : ℕ in atTop, ∀ r < n^100, (step n r).net.count ≤ C*(n+r+2)^b)
    (hcoeff : ∀ᶠ n : ℕ in atTop, ∀ x, BooleanChoice.pathCoefficient (fullVerifier (step n) (accept n)) x =
      signedWitness x) : BooleanChoice.PolynomialSignedVerifier := by
  refine ⟨3000+C*4^b+2*P*3^a, 100*(4+a+b), by omega, by positivity, ?_⟩
  filter_upwards [haccept, hstep, hcoeff, eventually_ge_atTop 1] with n hparse ht hc hn
  exact ⟨Hot.decodeGuessWidth n + n^100, fullVerifier (step n) (accept n),
    verifierBudget_le hn (fun r => (step n r.val).net.count) (Hot.decodeGuessWidth_le_cubic n)
      hparse (fun r => ht r r.isLt) (fullVerifier_count (step n) (accept n)), hc⟩

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI
