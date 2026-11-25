import OAI.Computability.QuantumFactoring.BooleanNetworkFurther
import OAI.LinearAlgebra.SpectralBooks.SignedWitness
import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Signed polynomial-size verifier circuits for the universal witness

The first output marks a positive contribution, and the second a negative
one. Guess bits can include uniquely checked auxiliary certificates.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace BooleanChoice
open ExactQuantumFactoring Filter

def pathCoefficient {n h : ℕ} (c : BooleanNetwork (n+h) 2) (x : Fin n → Bool) : ℤ :=
  ∑ g : Fin h → Bool,
    ((if c.eval (Fin.append x g) 0 then (1:ℤ) else 0) -
      (if c.eval (Fin.append x g) 1 then 1 else 0))

/-- A circuit family of polynomial arity and size whose signed counts are the
coefficients of the universal witness. -/
def PolynomialSignedVerifier : Prop :=
  ∃ C b : ℕ, 0 < C ∧ 0 < b ∧ ∀ᶠ n : ℕ in atTop,
    ∃ (h : ℕ) (c : BooleanNetwork (n+h) 2),
      n + h + c.net.count + 1 ≤ C * n^b ∧ ∀ x, pathCoefficient c x = signedWitness x

end BooleanChoice

end

end SpectralBooks
end LinearAlgebra
end OAI
