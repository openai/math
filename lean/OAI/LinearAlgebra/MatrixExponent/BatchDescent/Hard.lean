import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Compilation
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Encoded
import OAI.LinearAlgebra.MatrixExponent.Processor.Resistance
import OAI.LinearAlgebra.MatrixExponent.Tagged.Reduction

/-!
# Exact many-list hardness over finite fields

A failure of tagged permutation hardness supplies the compiled
descent. Applying it to the resistant family yields a contradiction.
The distinctness reduction retains the full range of batch sizes.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Filter

theorem hard (F : Type) [Field F] [Finite F] : Tagged.Hard F :=
  Processor.hard_of_descent (descent fun bad => compilation_of_encoded (encoded bad))

theorem manyList_full (F : Type) [Field F] [Finite F] :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ w : ℕ in atTop, ∀ t m : ℕ,
      1 ≤ t → (t : ℝ) ≤ (2 : ℝ) ^ ((w : ℝ) ^ (1 + η)) → Realizes F w t m →
      (t : ℝ) * listBits w * (w : ℝ) ^ η < m :=
  Tagged.manyList_full (hard F)

theorem manyList (F : Type) [Field F] [Finite F] : ManyList (Realizes F) :=
  Tagged.manyList_of_tag (hard F)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
