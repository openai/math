import OAI.Computability.NearSquareRoot.KernelAutomatonEquiv

/-! # Rational transfer matrices for finite column alphabets -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelAutomatonEquiv

/-- An explicit finite linear representation of a rational series on words. -/
structure Series (γ : Type*) where
  dim : ℕ
  initial : Fin dim → ℚ
  letter : γ → Matrix (Fin dim) (Fin dim) ℚ
  final : Fin dim → ℚ

namespace Series

/-- Evaluate the initial and final weights around the ordered product. -/
def eval {γ : Type*} (P : Series γ) (w : List γ) : ℚ := weight P.initial P.letter P.final w

/-- Compare all coefficients, at all word lengths. -/
def same {γ : Type*} [Fintype γ] (P Q : Series γ) : Bool :=
  equivalent P.initial P.letter P.final Q.initial Q.letter Q.final

theorem same_iff {γ : Type*} [Fintype γ] (P Q : Series γ) :
    P.same Q = true ↔ ∀ w, P.eval w = Q.eval w := equivalent_iff ..

end Series
end KernelAutomatonEquiv

end NearSquareRoot
end Computability
end OAI
