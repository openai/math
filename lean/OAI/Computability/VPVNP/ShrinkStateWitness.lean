import OAI.Computability.VPVNP.ShrinkMonomialWitness
import OAI.Computability.VPVNP.ShrinkStatePass
import OAI.Computability.VPVNP.NetworkMonomialIso

/-!
# Parameter witnesses of the shrinking pass on a compressor state

The change of coordinates that packs the old site and its lane for the
shrinking step pulls the old half-wire arguments back to their packed
forms. Every surviving local witness has the same formal exponent vector.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.State

open NetworkKernel MotifBlocks MotifGrid MotifConversion PackingData ShrinkMotif

variable {a b g : ℕ} {δ factor : ℝ} (X : State a (packingLaneBits a g))
variable {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable {R : Type*} [CommRing R] (κ : (parameterData B).Entry → R)
variable (hκ : (parameterData B).IsSolution κ)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- Classical equality test on base sites used to construct monomial witnesses for the
shrinking kernels. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- Every entry of every selected kernel in the dyadic shrinking state
pass is a finite sum of parameter monomials. The witnesses enumerate the
absorbed words and the accepted resident matrix checks. -/
noncomputable def shrinkStateKernelWitness :
    ∀ s v x z, MonomialWitness κ (((X.shrinkStatePass B κ hκ ready).step.term s).kernel v x z) := by
  let P := X.packingData
  let hc := two_le_packingColors a
  let hd := Nat.two_pow_pos a
  let order := X.shrinkOrder
  let step := P.shrinkStep B κ hκ hc hd X.shrinkNumber order X.packingWidth ready
    (X.shrinkStateIndex ready)
  exact step.reindexInputWitness X.packingInputIso
    (P.shrinkKernelWitness hc hd X.shrinkNumber order X.packingWidth B κ hκ ready
      (X.shrinkStateIndex ready))

/-- The parameter degree bound survives the coordinate change on the
old half-wire inputs of the state pass. -/
theorem shrinkStateKernelWitness_degree_le (s : X.ShrinkSelection B) (v x z)
    (w : (X.shrinkStateKernelWitness B κ hκ ready s v x z).Choice) {W : ℕ}
    (hW : ∀ e, X.width e ≤ W) :
    (∑ label, (X.shrinkStateKernelWitness B κ hκ ready s v x z).exponents w label) ≤
      (6 * (2 ^ a * pieceCount (2 ^ a) (2 * 2 ^ a + 1)) * fieldFactor B) * (W + 1) := by
  let P := X.packingData
  let hc := two_le_packingColors a
  exact P.shrinkKernelWitness_degree_le hc (Nat.two_pow_pos a) X.shrinkNumber X.shrinkOrder
    X.packingWidth B κ hκ ready (X.shrinkStateIndex ready) s v _ _ w (fun e ↦ hW _)

end Compression.State

end VPVNP
end Computability
end OAI
