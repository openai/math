import Complexity.Computability.Circuit.Arithmetic.VNP
import OAI.Computability.VPVNP.Classes
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Boolean witnesses in the two VNP models

Number the formal variables first and the witness variables second. With this ordering,
the two Boolean sums agree term by term after reindexing their assignments.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ComplexityLib

open MvPolynomial Cslib.Circuits.Arithmetic
open scoped Classical

/-- Number the output and witness variables in consecutive blocks. -/
def sumVariables {X W : Type} {a b : ℕ} (x : X ≃ Fin a) (w : W ≃ Fin b) :
    X ⊕ W ≃ Fin (a + b) :=
  (x.sumCongr w).trans finSumFinEquiv

/-- The Boolean witness sum commutes with numbering both blocks of variables. -/
theorem booleanSum_rename {K : Type*} [Field K] {X W : Type} [Fintype W] {a b : ℕ}
    (x : X ≃ Fin a) (w : W ≃ Fin b) (g : MvPolynomial (X ⊕ W) K) :
    booleanSum b (rename (sumVariables x w) g) =
      rename x (∑ y : W → Bool, witnessValue y g) := by
  rw [booleanSum, map_sum]
  refine Fintype.sum_equiv (w.symm.arrowCongr (Equiv.refl Bool)) _ _ fun e => ?_
  change projection (booleanAssignment e) (rename (sumVariables x w) g) =
    rename x (witnessValue (e ∘ w) g)
  induction g using MvPolynomial.induction_on with
  | C c => simp [witnessValue]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp, rename_X, projection_X]
    rcases i with i | j
    · simp [sumVariables, booleanAssignment, witnessValue]
    · cases h : e (w j) <;> simp [sumVariables, booleanAssignment, witnessValue, h]

end ComplexityLib

end VPVNP
end Computability
end OAI
