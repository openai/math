import OAI.LinearAlgebra.MatrixExponent.Rectangle.Weights
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Geometric closure of the rank locus in the full coefficient space -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k : ℕ}

def ZClosure {ι : Type} (s : Set (ι → F)) (x : ι → F) : Prop :=
  ∀ p : MvPolynomial ι F,
    (∀ y ∈ s, MvPolynomial.eval y p = 0) → MvPolynomial.eval x p = 0

abbrev Coordinates (i j k : ℕ) := Pos i k × Pos k j × Pos i j

def coefficients (w : Fin i → Fin j → Fin k → F) : Coordinates i j k → F :=
  fun (x, y, z) => if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then w x.1 y.2 x.2 else 0

def rankSet (F : Type*) [Field F] (i j k r : ℕ) : Set (Coordinates i j k → F) :=
  {v | ∃ (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F) (c : Fin r → Pos i j → F),
    ∀ x y z, ∑ l : Fin r, a l x * b l y * c l z = v (x, y, z)}

def BorderRankLE (w : Fin i → Fin j → Fin k → F) (r : ℕ) : Prop :=
  ZClosure (rankSet (AlgebraicClosure F) i j k r)
    (coefficients (fun x y z => algebraMap F (AlgebraicClosure F) (w x y z)))

end OAI.LinearAlgebra.MatrixExponent.Rectangle
