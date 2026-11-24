import OAI.Computability.VPVNP.DegreeRefreshEntries
import OAI.Computability.VPVNP.DegreeRefreshPass
import OAI.Computability.VPVNP.NetworkMonomialIso

/-!
# Scalar witnesses on the dyadic refresh pass

Splitting the old lane into port and remaining lane coordinates reindexes the
arguments of the two diagonal ties and the motif matrix entry at each port.
The accepting entry contributes its list of template labels to the pass.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.Refresh

open NetworkKernel SpectralGeometry DegreeRefresh MotifConversion

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (X : State a (a + g)) (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)
variable {R : Type*} [CommRing R] (κ : (parameterData F).Entry → R)
  (hκ : (parameterData F).IsSolution κ)

/-- Each refresh site checks its two diagonal ties and reads the selected
motif entry on its actual half-wire arguments. -/
noncomputable def dyadicRefreshKernelWitness :
    ∀ c v x z, MonomialWitness κ
      (((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term c).kernel v x z) := by
  let step := expanderRefreshStep (splitSlots X) (bitWordFinEquiv a) (splitWidths X)
    P hdH hconn F κ hκ hD hd
  exact step.reindexInputWitness (relaneIso X.slots (splitBitWord a g) X.width)
    (fun c ↦ expanderKernelWitness (splitSlots X) (bitWordFinEquiv a) (splitWidths X)
      P hdH hconn F hD hd c κ hκ)

/-- The exponents contributed at a physical port are bounded by the number
of internal ties times the largest old wire width. -/
theorem dyadicRefreshKernelWitness_degree_le (c : DyadicRefreshChoice X P hdH hconn F) (v x z)
    (b : (dyadicRefreshKernelWitness X P hdH hconn F hD hd κ hκ c v x z).Choice)
    {W : ℕ} (hw : ∀ e, X.width e ≤ W) :
    (∑ l, (dyadicRefreshKernelWitness X P hdH hconn F hD hd κ hκ c v x z).exponents b l) ≤
      Fintype.card (Tie (2 ^ a)) * W :=
  expanderKernelWitness_exponents (splitSlots X) (bitWordFinEquiv a) (splitWidths X)
    P hdH hconn F hD hd c κ hκ v _ _ b (fun _ ↦ hw _)

end Compression.Refresh

end VPVNP
end Computability
end OAI
