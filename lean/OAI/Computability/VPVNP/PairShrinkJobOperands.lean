import OAI.Computability.VPVNP.PairShrinkHandlerPrepared
import OAI.Computability.VPVNP.PairShrinkPartyNative
import OAI.Computability.VPVNP.PairShrinkHiddenReadback

/-!
# Resident map arguments after the party gather

The placed child packets supply C and D. The party gather writes the AB and
surviving words and preserves both the child argument arena and the earlier
absorbed slots. These facts identify the private words passed to the
selected grouped map for any local tensor argument.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open Compression.ShrinkEnergy MotifBlocks MotifGrid MotifConversion NetworkKernel
open CompressorRecords CompressorRecords.ShrinkSlots CompressorRecords.ShrinkSliceSweep
open NodeArguments
open scoped Fin.CommRing

variable {a b g w endAddr : ℕ} {δ factor : ℝ} {K : Type} [_root_.Field K]
variable {X : State a (packingLaneBits a g)}
variable {F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
variable {ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ} {sel : X.ShrinkSelection F}
variable {m : X.packingData.Motif} {party : Fin 6}
variable (J : Job X F ready sel m party w)
/-- Classical decidable equality on the compression state’s base vertices for the resident map
operands assembled by the party gather. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X F sel
local notation "widths" => ShrinkPreparedCall.width F X sel
local notation "owner" => X.packingData.shrinkPartySite side m party
local notation "Idx" => Fin.val (ShrinkMotifOrder.stateNumber X m)

/-- All independent child half-wires stored at this parent. This is the
pointwise packet conclusion of the child scan, reindexed by the old layout. -/
def Job.ChildWords (priv : Word w → Word w) (endAddr : ℕ) : Prop :=
  ∀ site (eqn : X.packingData.shrinkPartySite side m party = packedSiteEquiv site),
    ShrinkOldHalves.PlacedPackets X side J.arena J.nodes priv site
      (X.packingData.shrinkPlacedHalf X.packingWidth side site eqn J.old) endAddr

variable {before after : Word w → Word w}

/-- After all interval copies the two old CD endpoints retain their original
child bits, and the assembled AB endpoint has its computed value. -/
theorem Job.Assembled.demandFields (staged : J.Assembled before after)
    (child : J.ChildWords before endAddr)
    (endBefore : ∀ u, J.arena.base (J.nodes u) + J.arena.stride ≤ J.scratch.staging) :
    ShrinkCallDemandCells.Readback X side m party J.arena J.nodes J.old after
      J.scratch.staging endAddr := by
  refine ⟨staged.ab, ?_, ?_⟩
  · intro hp
    subst party
    apply ShrinkCallDemandCells.placedPackets_frame X side J.arena J.nodes _ endBefore staged.below
    exact child _ (X.packingData.shrinkPartySite_C side m)
  · intro hp
    subst party
    apply ShrinkCallDemandCells.placedPackets_frame X side J.arena J.nodes _ endBefore staged.below
    exact child _ rfl

variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X F sel))
  (internalLabel (ShrinkPreparedCall.width F X sel) (selectedLayout X F sel))
  (X.packingData.shrinkPartySite (selectedLayout X F sel) m party))

set_option maxHeartbeats 1200000 in
-- Unfolding the selected layout identifies the hidden coordinate and its dependent bit width.
/-- Turn the completed native hidden-word readback at the current owner into
the caller's physical private field predicate. -/
theorem Job.hiddenFields (raw : ∀ t (owned : owner = X.packingData.shrinkInternalOwner side (m, t))
    (i : Fin ((widths) m (!side, t))),
    before ((ShrinkHiddenSlots.address X J.scratch.hidden J.scratch.stride (m, t) + i.val : ℕ) :
      Word w) = PrivateFields.bitValue w (RAMSerialization.wordBits _ (hidden (m, t) owned) i)) :
    ShrinkCallSupplyCells.Absorbed X side (widths) m party J.scratch hidden before := by
  intro t own i
  simpa only [ShrinkHiddenSlots.address, ShrinkHiddenSlots.id_eq, ShrinkCallFields.Scratch.shared]
    using raw t own i

set_option maxHeartbeats 1200000 in
-- The private readback uses the selected layout at the dependent old and new fiber types.
/-- The independent input of an absorbed edge is still available at both
ends after the subsequent copies. -/
theorem Job.Assembled.hiddenFields (staged : J.Assembled before after)
    (prior : ShrinkCallSupplyCells.Absorbed X side (widths) m party J.scratch hidden before)
    (count : Idx < J.scratch.motifs) (fit : ∀ t, (widths) m (!side, t) ≤ J.scratch.stride) :
    ShrinkCallSupplyCells.Absorbed X side (widths) m party J.scratch hidden after := by
  intro t own i
  have hi := i.isLt.trans_le (fit t)
  have upper := J.scratch.shared_end count t
  have lt : J.scratch.shared Idx t + i.val < J.scratch.staging := by omega
  rw [staged.below _ ((Nat.mod_le ..).trans_lt lt)]
  exact prior t own i

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
