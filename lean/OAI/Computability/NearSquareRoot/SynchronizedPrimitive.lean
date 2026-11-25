import OAI.Computability.NearSquareRoot.SynchronizedPair
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! # Primitive local layers of the synchronized short transform

A matched stage uses disjoint pairs. Both the forward and adjoint pairs admit
the same three normalized Walsh rounds with unit phases between rounds.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedPair
open scoped Matrix

/-- One permutation, phase table, or complete matching of phase-factorable pairs. -/
inductive ShortLayer {A : Type} [DecidableEq A] : Matrix A A ℂ → Prop
  | permutation (e : Equiv.Perm A) :
      ShortLayer (fun i j => if i = e j then 1 else 0)
  | phase (d : A → ℂ) (hd : ∀ i, ‖d i‖ = 1) :
      ShortLayer (Matrix.diagonal d)
  | pairs {I : Type} [DecidableEq I] (e : (Fin 2 × I) ≃ A)
      (f : I → SynchronizedPair.PairMatrix) (hf : ∀ i, ThreeWalsh (f i))
      (hfa : ∀ i, ThreeWalsh ((f i)ᴴ)) :
      ShortLayer ((Matrix.blockDiagonal f).submatrix e.symm e.symm)

end ShortFourier

end NearSquareRoot
end Computability
end OAI
