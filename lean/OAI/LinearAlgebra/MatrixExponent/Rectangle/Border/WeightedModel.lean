import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Model
import OAI.LinearAlgebra.MatrixExponent.Spectral.Semiring


/-! # The three tensor legs of a weighted product -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Spectral

variable {F : Type} [Field F] {i j k : ℕ}

def tripleLeg {α : Fin 3 → Sort*} (a : α 0) (b : α 1) (c : α 2) : ∀ t, α t :=
  Fin.cases a (Fin.cases b (Fin.cases c fun t => Fin.elim0 t))

abbrev legs (i j k : ℕ) : Fin 3 → Type := ![Pos i j, Pos i k, Pos k j]

instance legFintype (i j k : ℕ) : ∀ s, Fintype (legs i j k s) :=
  tripleLeg (inferInstanceAs (Fintype (Pos i j))) (inferInstanceAs (Fintype (Pos i k)))
    (inferInstanceAs (Fintype (Pos k j)))

def ungroup (x : ∀ s, legs i j k s) : Coordinates i j k := (x 1, x 2, x 0)

def wtensor (T : Coordinates i j k → F) : Tensor F (Fin 3) :=
  Tensor.ofRaw (Raw.ofTable (legs i j k) (T ∘ ungroup))

def weightedTensor (w : Fin i → Fin j → Fin k → F) := wtensor (coefficients w)

end OAI.LinearAlgebra.MatrixExponent.Rectangle
