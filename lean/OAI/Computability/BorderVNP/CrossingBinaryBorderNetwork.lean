import OAI.Computability.BorderVNP.CrossingBorderNetwork
import OAI.Computability.BorderVNP.CrossingFusionBinary

/-!
# Border shortening for the binary-field encoding of the fused sides

The state rank and crossing modes may occupy separately rounded binary fields.
The concrete decoding identity uses the dynamic-programming state numbering and
still gives an exact antipodal contraction. The two extra padded bridge groups
are charged in the same width estimate as the mixed-radix construction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

variable {D p m r : ℕ} {K : Type*} [Field K]

/-- Independent approximations of the explicitly checkable binary first sides produce
an exact shortening identity after one tensor power. -/
theorem paidIdentity_of_binary_sides (hm : 0 < m) (w : WireStates (leastEnergy m) (2^m))
    (addr : CutBit D (2*leastEnergy m) (stateCountAt (D*leastEnergy m)) ↪ Fin p × Fin m)
    (hD : 441 ≤ D) (hp : (p : ℝ) ≤ 21/20 * Real.sqrt D)
    (hlarge : 100 ≤ (m : ℝ) * Real.sqrt D)
    (hrank : (r : ℝ) ≤ (2 : ℝ) ^ (1/50 * m * Real.sqrt D))
    (hA : ∀ o, fieldSide K (binarySide w addr) true o ∈
      imageClosure (balancedCutSums (Fin D ⊕ Fin p) (Fin (2^m)) K r))
    {c₀ : ℝ} (hc : 6 * c₀ ^ 2 < 1/500) (hdir : (D : ℝ) ≤ c₀ * Real.sqrt m) :
    ∃ t : ℕ, 0 < t ∧ Nonempty (PaidIdentity K D (t*m)) :=
  paidIdentity_of_decomposition hm (binarySide w addr) (binarySide_identity w addr)
    hD hp hlarge hrank hA hc hdir

end Crossing

end BorderVNP
end Computability
end OAI
