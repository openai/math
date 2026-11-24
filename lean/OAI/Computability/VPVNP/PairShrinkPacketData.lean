import OAI.Computability.VPVNP.PairShrinkJobOperands

/-!
# Packet premises of the resident shrinking-party gather

The child scan supplies the old half-wires at the AB endpoints. The stored
parent supplies the surviving half-wires. The selected map's workspace fit
bounds all nine staging intervals.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif
open MotifGrid MotifBlocks MotifConversion CompressorRecords CompressorRecords.ShrinkSlots
open NodeArguments

variable {a b g w n limit t endAddr : ℕ} {δ factor : ℝ} {K : Type} [_root_.Field K]
variable {X : State a (packingLaneBits a g)}
variable {F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
variable {ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ} {sel : X.ShrinkSelection F}
variable {m : X.packingData.Motif} {party : Fin 6}
variable (J : Job X F ready sel m party w) {priv : Word w → Word w}
/-- Use the same classical equality as the selected old half-wire layout. -/
private noncomputable local instance packetBase : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X F sel
local notation "site" => X.packingData.shrinkPartySite side m party
local notation "parentPacket" => Packet.mk J.node (packed (X.shrinkNext F ready sel) site J.parent)
local notation "demand" => ShrinkPreparedCall.widthsDemand X m

/-- The gather's input and staging requirements follow from the actual packet
readbacks and the workspace fit for this motif. -/
theorem Job.packets_of (child : J.ChildWords priv endAddr)
    (oldEnd : ∀ u, J.arena.base (J.nodes u) + J.arena.stride ≤ J.scratch.staging)
    (parentFit : (parentPacket).Fits J.arena w endAddr)
    (parentStored : (parentPacket).Stored J.arena (DFS.scratch endAddr priv))
    (parentEnd : J.arena.base J.node + (parentPacket).bits.length ≤ J.scratch.staging)
    (ok : ShrinkCallFields.Fits (w := w) (n := n) (limit := limit) (t := t)
      (u := repetitions F (demand)) F (demand) (sel m).val J.scratch
      (ShrinkMotifOrder.stateNumber X m).val (ShrinkCallDemandCells.cdBase X m J.arena J.nodes)) :
    J.Packets endAddr priv := by
  have room := ok.room.trans_lt ok.capacity.room
  unfold ShrinkCallFields.Scratch.target ShrinkCallFields.Scratch.source
    ShrinkCallFields.Scratch.descriptor at room
  have directory : J.scratch.directory < 2 ^ w := by omega
  have abEnd : J.scratch.staging + J.scratch.stride ≤ J.scratch.directory := by
    unfold ShrinkCallFields.Scratch.directory
    omega
  have supplyStride (k : Fin 4) : branchWidth X F sel m k ≤ J.scratch.stride :=
    ok.supply (side, k)
  refine ⟨?_, oldEnd, parentFit, parentStored, parentEnd, ok.ab, ?_, supplyStride, ?_⟩
  · intro dir hit
    cases dir <;> subst party <;> exact child _ rfl
  · exact (Nat.add_le_add_left ok.ab _).trans_lt (abEnd.trans_lt directory)
  · intro dir k
    exact (Nat.add_le_add_left (supplyStride k) _).trans_lt
      ((J.scratch.surviving_end dir k).trans_lt directory)

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
