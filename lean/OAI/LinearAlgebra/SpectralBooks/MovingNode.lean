import OAI.LinearAlgebra.SpectralBooks.SiteTensor.MovingTensor

/-! # The normalized log price at an exterior splitting node

The node carries the accumulated price of the exterior wires. This common
amount is subtracted at the interior and at every endpoint of the cube.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace SiteTensor.Relocation

variable {r : ℕ} {J : Type} {K : Type*} {q : Fin r → ℕ}

/-- A nonzero state together with its accumulated exterior wire price. -/
abbrev MovingNode (J : Type) (K : Type*) [Zero K] {r : ℕ} (q : Fin r → ℕ) :=
  {s : MovingTensor J K q // s.T.coeff ≠ 0} × ℝ

/-- Corrected value of an actual moving tensor at a placement. -/
def movingNodePrice [Fintype J] [Nonempty J] [Field K]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (scale : ℝ)
    (x : MovingNode J K q) (p : Fin r → J) : ℝ :=
  rawLogPrice φ scale (x.1.val.grouped p) - x.2

/-- Placement supplied by the endpoint choices in a Boolean cube. -/
def cornerAt (a b : Fin r → J) (x : Fin r → Bool) (i : Fin r) : J :=
  if x i then b i else a i

theorem cornerAt_update (a b : Fin r → J) (x : Fin r → Bool) (i : Fin r) (k : Bool) :
    cornerAt a b (Function.update x i k) =
      Function.update (cornerAt a b x) i (if k then b i else a i) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [cornerAt]
  · simp [cornerAt, Function.update_of_ne h]

end SiteTensor.Relocation

end

end SpectralBooks
end LinearAlgebra
end OAI
