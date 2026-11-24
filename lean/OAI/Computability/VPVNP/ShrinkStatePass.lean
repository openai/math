import OAI.Computability.VPVNP.ShrinkStep
import OAI.Computability.VPVNP.ShrinkingSlots
import OAI.Computability.VPVNP.SlotBundleNumbering
import OAI.Computability.VPVNP.ShrinkStateOutput

/-!
# A shrinking pass on a compressor state

Both numberings of each thick bundle are fixed before the local identities
are applied. The term choices then determine the layout and the widths of
the indexed output slots. The resulting state has the output degree and
unconsumed lane length required by the block schedule.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.State

open NetworkKernel MotifBlocks MotifGrid MotifConversion PackingData
open ShrinkMotif ShrinkEnergy SurvivingSlots

variable {a b g : ℕ} {δ factor : ℝ} (X : State a (packingLaneBits a g))

/-- Classical equality test on base sites used in the dyadic shrinking pass. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- The dyadic coloring has enough coordinates for two distinct endpoint colors. -/
theorem two_le_packingColors (a : ℕ) : 2 ≤ 2 * 2 ^ a + 1 := by
  have := Nat.two_pow_pos a
  omega

/-- Use the same finite base enumeration as the dyadic coloring and offset scans. -/
abbrev shrinkBaseOrder := X.baseIndex

/-- Number surviving slots by the mixed-radix keys of the lane-zero IDs. -/
noncomputable def shrinkStateIndex (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (layout : Bool) :=
  let m := subdivisions (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b)
  orderedDyadicSurvivingSlots X.slots X.baseIndex layout m ready.degree_budget

/-- Order the CD pieces by their lane-relative old arc identifiers. -/
noncomputable abbrev shrinkNumber :=
  X.packingData.sortedBundleNumbering X.shrinkBaseOrder
    (bitWordFinEquiv (packingTagBits (2 ^ a))) (two_le_packingColors a)

/-- Concatenate old thick wires in the common binary coordinate order. -/
noncomputable abbrev shrinkOrder :=
  X.packingData.sortedThickNumbering (two_le_packingColors a)

variable {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- A choice of one admitted local term on each CD occurrence. -/
noncomputable abbrev ShrinkSelection :=
  ∀ m, X.packingData.ShrinkChoice X.shrinkNumber X.packingWidth B m

/-- The next state determined by one entire list of motif selections. -/
noncomputable def shrinkNext (s : X.ShrinkSelection B) : State b g :=
  let p := equalArcMass (Position X.Base (BitWord a) (BitWord (packingTagBits (2 ^ a)))
    (BitWord g) (2 * 2 ^ a + 1)) (2 ^ a)
  let w := X.packingData.termWidths B X.shrinkNumber X.packingWidth s
  let l := chosenLayout p (fun e ↦ (relativeMass e : ℝ)) w
  X.shrinkOutputState l (subdivisions (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b))
    (fun m t ↦ w m l t) (X.shrinkStateIndex ready l)

theorem shrinkNext_positions (s : X.ShrinkSelection B) :
    X.positions = (2 ^ (2 * 2 ^ a + 1) * 2 ^ a) * (X.shrinkNext B ready s).positions :=
  X.shrinkOutputState_positions _ _ _ _

/-- Equation (7.2) in the coordinates retained between compressor substeps. -/
theorem shrinkNext_energy (hδ : δ < 1) (hf : 0 ≤ factor) (s : X.ShrinkSelection B) :
    (X.shrinkNext B ready s).energy ≤
      factor / (2 * (1 - δ)) * X.energy +
      roundingConstant (2 ^ a) (2 ^ b) (pieceCount (2 ^ a) (2 * 2 ^ a + 1))
        factor B.energyConstant (1 - δ) (subdivisions (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b)) *
        (X.positions : ℝ) ^ 2 := by
  unfold shrinkNext
  rw [shrinkOutputState_energy, X.energy_packingWidth, X.positions_packing]
  exact X.packingData.packed_energy_from_terms B X.shrinkNumber X.packingWidth s
    (two_le_packingColors _) (Nat.two_pow_pos _) ready hδ hf

variable {R : Type*} [CommRing R] (κ : (parameterData B).Entry → R)
variable (hκ : (parameterData B).IsSolution κ)

/-- The exact shrinking identity on a compressor state. Every term carries
its own subsequent state with the prescribed output degree and remaining lane. -/
noncomputable def shrinkStatePass (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ) :
    StatePass R X b g where
  step := X.reindexPackingStep (X.packingData.shrinkStep B κ hκ (two_le_packingColors a)
    (Nat.two_pow_pos a) X.shrinkNumber
    X.shrinkOrder X.packingWidth ready (X.shrinkStateIndex ready))
  next := X.shrinkNext B ready
  output_eq _ := rfl

theorem shrinkStatePass_positions (s : X.ShrinkSelection B) :
    X.positions = (2 ^ (2 * 2 ^ a + 1) * 2 ^ a) *
      ((X.shrinkStatePass B κ hκ ready).next s).positions := X.shrinkNext_positions B ready s

theorem shrinkStatePass_energy (hδ : δ < 1) (hf : 0 ≤ factor) (s : X.ShrinkSelection B) :
    ((X.shrinkStatePass B κ hκ ready).next s).energy ≤
      factor / (2 * (1 - δ)) * X.energy +
      roundingConstant (2 ^ a) (2 ^ b) (pieceCount (2 ^ a) (2 * 2 ^ a + 1))
        factor B.energyConstant (1 - δ) (subdivisions (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b)) *
        (X.positions : ℝ) ^ 2 := X.shrinkNext_energy B ready hδ hf s

end Compression.State

end VPVNP
end Computability
end OAI
