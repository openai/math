import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Mask
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Pairing
import OAI.LinearAlgebra.TensorSpectrum.Additive.RankAnalysis
import OAI.LinearAlgebra.MatrixExponent.LocalTensor
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Choosing coefficients for the upper bound

The tensor semiring is monomorphic. To reuse it without assuming
characteristic zero, choose an algebraically closed counterexample if one
exists. The tensor argument only uses the field axioms and algebraic closure.
-/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent

structure ClosedField where
  carrier : Type
  [field : Field carrier]
  [closed : IsAlgClosed carrier]

attribute [instance] ClosedField.field ClosedField.closed

instance : Nonempty ClosedField := ⟨⟨AlgebraicClosure ℚ⟩⟩

def Rectangle.DiscreteBound (F : Type*) [Field F] : Prop :=
  ∀ A B C : ℕ, 0 < A → 0 < B → 0 < C →
    Rectangle.exponent F ((A : ℝ) * B) ((A : ℝ) * C) ((B : ℝ) * C) ≤ ((A : ℝ) + B + C) ^ 2 / 4

/-- Field-independent consequences of the shared-tag inequality. No
law assumes square equality or any conjecture about spectral contacts. -/
structure Fulfills (F : Type) [Field F] : Prop where
  discrete : Rectangle.DiscreteBound F
  density : Rectangle.DensityBound F
  cells : Rectangle.CellBound F
  binary : Rectangle.Profile.BinaryLaw F
  degrees : Rectangle.Sparse.DegreeBound F

def candidate : ClosedField :=
  Classical.epsilon (fun k : ClosedField => ¬ Fulfills k.carrier)

abbrev Coeff := candidate.carrier

theorem closed_laws (h : Fulfills Coeff) (K : Type) [Field K] [IsAlgClosed K] :
    Fulfills K := by
  by_contra bad
  have ex : ∃ k : ClosedField, ¬ Fulfills k.carrier := ⟨⟨K⟩, bad⟩
  exact Classical.epsilon_spec ex h

theorem exists_nonzero_nodes {F : Type*} [Field F] [Infinite F] (n : ℕ) :
    ∃ nodes : Fin n → F, Function.Injective nodes ∧ ∀ i, nodes i ≠ 0 := by
  let e : Fin n ↪ ({0}ᶜ : Set F) :=
    Fin.valEmbedding.trans ((Set.finite_singleton (0 : F)).infinite_compl.natEmbedding _)
  exact ⟨fun i => e i, Subtype.val_injective.comp e.injective, fun i => (e i).property⟩

end OAI.LinearAlgebra.MatrixExponent

namespace OAI.LinearAlgebra.MatrixExponent.Upper
open OAI.MatrixMultiplication.Foundation

def matrixTensor (a b c : ℕ) :
    Tensor Coeff (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  Tensor.matrixCoefficients (Fin a) (Fin b) (Fin c)

end OAI.LinearAlgebra.MatrixExponent.Upper
