import OAI.Computability.VPVNP.ShrinkHistory
import OAI.Computability.VPVNP.ShrinkStatePass
import OAI.Computability.VPVNP.StatePassHistory

/-!
# History bounds for the actual dyadic shrinking pass

For each admissible selection the records contain its resident maps,
absorbed fields and map arguments together with all old and new half-wire
fields. The bound for this substep depends only on the two degree exponents
and the fixed conversion block. It applies uniformly at every packed site.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.State

open NetworkKernel MotifBlocks MotifGrid MotifConversion PackingData ShrinkMotif ShrinkEnergy

variable {a b g : ℕ} {δ factor : ℝ} (X : State a (packingLaneBits a g))
variable {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable {R : Type*} [CommRing R] (κ : (parameterData B).Entry → R)
variable (hκ : (parameterData B).IsSolution κ)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

open Classical in
/-- Records of the selected six-party kernels before adding the actual
old and new incident half-words. -/
noncomputable def shrinkExtraRecords : (X.shrinkStatePass B κ hκ ready).Records :=
  fun s v ↦ X.packingData.shrinkSiteRecords X.shrinkNumber X.packingWidth B s
    (X.packingData.shrinkTermLayout B X.shrinkNumber X.packingWidth s) v

/-- The fixed per-substep history growth factor. `K` counts old positions
and `r = dQ` counts occurrences of each packed role. -/
noncomputable def shrinkHistoryFactor (a b : ℕ) : ℕ :=
  let d := 2 ^ a
  let c := 2 * d + 1
  let K := 2 ^ c * d
  let r := d * pieceCount d c
  let D := 1 + 6 * r + 4 * r + (6 * r) * 10
  max (D + K * (2 * d) + 2 * 2 ^ b + K) (max 1 (fieldFactor B) + 1)

/-- The exact state pass has the bounded local histories used in Theorem 7.1. -/
theorem shrinkStatePass_bounded :
    (X.shrinkStatePass B κ hκ ready).Bounded
      ((X.shrinkStatePass B κ hκ ready).slotRecords (X.shrinkExtraRecords B κ hκ ready))
      (shrinkHistoryFactor B a b) := by
  classical
  let P := X.packingData
  let d := 2 ^ a
  let c := 2 * d + 1
  let r := d * pieceCount d c
  have hc := two_le_packingColors a
  have hd := Nat.two_pow_pos a
  have hw (x) : X.packingWidth x ≤ X.maxWireWidth := X.width_le_maxWireWidth _
  apply StatePass.slotRecords_bounded _ _ (2 ^ c * d)
    (1 + 6 * r + 4 * r + (6 * r) * 10) (max 1 (fieldFactor B)) (le_max_left ..)
  · intro i v
    have h := P.card_reindexed_shrinkPlace (P.shrinkTermLayout B X.shrinkNumber X.packingWidth i)
      v (packingInputSites X.Base a g) (by omega)
    rw [← Nat.card_eq_fintype_card]
    exact h.le
  · intro i v
    exact P.shrinkSiteRecords_count_le X.shrinkNumber X.packingWidth B i _ v hc
  · intro i v
    exact P.shrinkSiteRecords_largest_le X.shrinkNumber X.packingWidth B i _ v hc hd hw
  · intro i e
    let l := P.shrinkTermLayout B X.shrinkNumber X.packingWidth i
    exact (P.shrinkSlotWidth_le hc hd X.shrinkNumber X.packingWidth hw B i l
      (subdivisions d c (2 ^ b)) (X.shrinkStateIndex ready l).outgoing e).trans
        (Nat.mul_le_mul_right _ (le_max_right ..))

end Compression.State

end VPVNP
end Computability
end OAI
