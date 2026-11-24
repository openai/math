import OAI.Computability.VPVNP.PairShrinkChildWords
import OAI.Computability.VPVNP.PairShrinkCallFrameStores

/-!
# Resident inputs immediately after the shrinking hidden scan

The child scan stores one packet per preceding site. The hidden scan writes
above all of those packets and above the popped parent's own arguments.
It supplies the single shared value used at both ends of an absorbed edge.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel LocalHistory
open MotifBlocks MotifConversion MotifGrid CompressorRecords CompressorRecords.ShrinkSlots
open NodeArguments DFS
open scoped Fin.CommRing

variable {a b g w endAddr : ℕ} {factor δ : ℝ} {K : Type} [_root_.Field K]
variable {X : State a (packingLaneBits a g)}
variable {F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
variable {ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ} {sel : X.ShrinkSelection F}
private noncomputable local instance firstMapBase : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X F sel
local notation "widths" => ShrinkPreparedCall.width F X sel
variable (v : (X.Base × BitWord (packingTagBits (2 ^ a))) × BitWord g)
variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X F sel))
  (internalLabel (ShrinkPreparedCall.width F X sel) (selectedLayout X F sel)) v)
variable (q : X.packingData.ResidentMap (selectedLayout X F sel) v)
variable (J : Job X F ready sel q.1.1 q.1.2 w)
local notation "rows" => ShrinkHiddenSlots.rows X side widths v hidden
local notation "upper" => J.scratch.hidden
local notation "pitch" => J.scratch.stride
variable (childMem : Word w → Word w)
local notation "after" => ShrinkHiddenGuess.storeRows upper pitch rows childMem

include q in
/-- Both families of inputs used by the first resident come from the same
concrete memory after the once-per-field guess. -/
theorem Job.firstMapFields (children : J.ChildWords childMem endAddr)
    (oldEnd : ∀ u, J.arena.base (J.nodes u) + J.arena.stride ≤ upper)
    (size : ∀ m t, widths m (!side, t) ≤ pitch)
    (cap : upper + (ShrinkHistoryRows.hiddenOrder X).length * pitch ≤ 2 ^ w) :
    J.ChildWords after endAddr ∧
      ShrinkCallSupplyCells.Absorbed X side widths q.1.1 q.1.2 J.scratch (q.2.symm ▸ hidden)
        after := by
  have fit := ShrinkHiddenSlots.rows_fit X upper pitch side widths v hidden size cap
  constructor
  · intro site h
    apply ShrinkCallDemandCells.placedPackets_frame X side J.arena J.nodes (children site h) oldEnd
    intro cell low
    exact ShrinkCallFrameLive.hidden_below upper pitch rows cell (fun r hr ↦ (fit r hr).2) low
  · rcases q with ⟨⟨m, j⟩, owner⟩
    change X.packingData.shrinkPartySite side m j = v at owner
    subst v
    apply Job.hiddenFields J hidden
    intro t owned i
    exact ShrinkHiddenSlots.resident_read X J.scratch.hidden J.scratch.stride side widths _
      hidden childMem fit (m, t) owned i

/-- The popped parent argument survives the older-child writes and the
upper-region hidden writes before the surviving-interval gather reads it. -/
theorem Job.parentStored_after_fields (parent : Packet) (original : Scratch w endAddr)
    (childPackets : List Packet) (childFit : ∀ z ∈ childPackets, z.Fits J.arena w endAddr)
    (distinct : ∀ z ∈ childPackets, z.node ≠ parent.node)
    (written : DFS.scratch endAddr childMem = writePackets J.arena childPackets original)
    (pfit : parent.Fits J.arena w endAddr) (present : parent.Stored J.arena original)
    (oldEnd : J.arena.base parent.node + parent.bits.length ≤ upper)
    (size : ∀ m t, widths m (!side, t) ≤ pitch)
    (cap : upper + (ShrinkHistoryRows.hiddenOrder X).length * pitch ≤ 2 ^ w) :
    parent.Stored J.arena (DFS.scratch endAddr after) := by
  have kept : parent.Stored J.arena (DFS.scratch endAddr childMem) := written ▸
    writePackets_preserves J.arena childPackets parent original childFit pfit distinct present
  have fit := ShrinkHiddenSlots.rows_fit X upper pitch side widths v hidden size cap
  apply kept.congr
  intro i
  let addr : Word w := ((J.arena.base parent.node + i.val : ℕ) : Word w)
  have val : addr.val = J.arena.base parent.node + i.val := Nat.mod_eq_of_lt
    ((Nat.add_lt_add_left i.isLt _).trans_le pfit.2.2)
  have lo : endAddr ≤ addr.val := val ▸ pfit.1.trans (Nat.le_add_right ..)
  have hi : addr.val < upper := val ▸ (Nat.add_lt_add_left i.isLt _).trans_le oldEnd
  change rawScratch (DFS.scratch endAddr after) addr =
    rawScratch (DFS.scratch endAddr childMem) addr
  simpa only [rawScratch, dite_eq_left lo, DFS.scratch] using
    ShrinkCallFrameLive.hidden_below upper pitch rows addr (fun r hr ↦ (fit r hr).2) hi

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
