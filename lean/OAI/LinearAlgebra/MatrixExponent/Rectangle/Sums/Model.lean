import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.WeightedModel

/-!
# A sum of independently weighted products

The site order throughout is output, left input, right input.
The spectral tensor semiring uses direct sum and tensor product.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sums
open Spectral Filter

structure Shape where
  i : ℕ
  j : ℕ
  k : ℕ
  hi : 0 < i
  hj : 0 < j
  hk : 0 < k

abbrev Weights (F : Type) (v : Shape) := Fin v.i → Fin v.j → Fin v.k → F
abbrev Three (F : Type) [Field F] := Tensor F (Fin 3)

variable {F : Type} [Field F] {n : ℕ}

def rank (A : Three F) : ℕ := sInf {r : ℕ | A ≤ (r : Three F)}

def asymptotic (A : Three F) : ℝ :=
  limUnder atTop fun t : ℕ => (rank (A ^ t) : ℝ) ^ (t : ℝ)⁻¹

def blocks (v : Fin n → Shape) (w : ∀ t, Weights F (v t)) : Three F :=
  ∑ t, weightedTensor (w t)

def unweighted (F : Type) [Field F] (v : Fin n → Shape) : ∀ t, Weights F (v t) :=
  fun _ _ _ _ => 1

def entropy (p : Fin n → ℝ) := -(∑ i, p i * Real.log (p i))

def mean (v : Fin n → Shape) (p : Fin n → ℝ) (q : Shape → ℕ) :=
  ∑ i, p i * Real.log (q (v i))

def objective (L : ℝ → ℝ → ℝ → ℝ) (v : Fin n → Shape) (p : Fin n → ℝ) :=
  entropy p + L (mean v p Shape.i) (mean v p Shape.j) (mean v p Shape.k)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sums
