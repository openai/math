import Mathlib.LinearAlgebra.Vandermonde

/-! # Geometric evaluation over a commutative ring -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {K : Type*} [CommRing K]

/-- Evaluation at the nodes `1, q, ..., q^(a-1)` in the monomial basis. -/
def geometricMatrix (a : ℕ) (q : K) : Matrix (Fin a) (Fin a) K :=
  vandermonde (fun i ↦ q ^ i.val)

@[simp] theorem geometricMatrix_apply (a : ℕ) (q : K) (i j : Fin a) :
    geometricMatrix a q i j = q ^ (i.val * j.val) := by
  simp [geometricMatrix, vandermonde_apply, pow_mul]

end FiniteFourier
end LinearAlgebra
end OAI
