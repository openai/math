import OAI.LinearAlgebra.FiniteFourier.GeometricMatrix

/-! # Coordinate matrix of the dyadic prime-axis splitting

The singleton coordinate records the augmentation. The nonzero addresses are
indexed in multiplicative-orbit order and the binomial basis is in frequency order.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
namespace Deformation

variable {R : Type*} [CommRing R] {m : ℕ}

/-- Forward coordinates for the scalar and binomial CRT summands. The address
`none` is the cyclic zero address on input and the augmentation on output. -/
def dyadicPrimeForwardMatrix (z : Fin m) (u : Rˣ) (hm : IsUnit (m : R))
    (d : Fin m → Rˣ) : Matrix (Option (Fin m)) (Option (Fin m)) R
  | none, _ => 1
  | some j, none => if j = z then 1 else 0
  | some j, some t => (↑hm.unit⁻¹ : R) * (d j : R) * (u : R) ^ (j.val * t.val)

end Deformation

end

end FiniteFourier
end LinearAlgebra
end OAI
