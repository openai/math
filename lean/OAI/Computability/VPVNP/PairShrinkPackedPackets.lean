import OAI.Computability.VPVNP.PairShrinkCanonicalPacketBounds
import OAI.Computability.VPVNP.PairShrinkPacketData
import OAI.Computability.VPVNP.PairShrinkPackedCapacity
import OAI.Computability.VPVNP.PairShrinkPackedParent

/-!
# Fitted packet gathers on every selected packed shrinking level

The old and new row addresses come from the selected level and its successor.
The terminal arguments occupy a separate private interval before the map
scratch. Only the child and parent bit readbacks depend on the private memory
at entry to an individual resident job.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCanonicalJob

open BurstRAM Compression Compression.ShrinkMotif CompressorRecords NodeArguments
open DescriptorSpace ShrinkBlockInputs ShrinkSlots ShrinkCallCapacity ShrinkCallFields
open CursorNetwork CursorBounds TraversalRoles TraversalRows Filter MotifConversion

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)

section Job

variable (j : Fin S.steps) {g w : ℕ} (X : State (a j) (packingLaneBits (a j) g))
variable (sel : SelectedScore.Selection B X) (m : X.packingData.Motif) (party : Fin 6)
/-- The packet structure uses the selected layout's equality on the old sites. -/
private noncomputable local instance packedJobBase : DecidableEq X.Base := Classical.decEq _
variable (J : ShrinkPartyNative.Job X B.shrink (S.shrink j) sel m party w)
local notation "Y" => X.shrinkNext B.shrink (S.shrink j) sel
local notation "owner" => X.packingData.shrinkPartySite (selectedLayout X B.shrink sel) m party
local notation "packet" => Packet.mk J.node (packed Y owner J.parent)
local notation "demand" => X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m

/-- Concrete address fits and the memory-dependent packet constructor needed
by the selected resident map stage. -/
structure PacketSpace (n limit : ℕ) : Prop where
  fields : Fits (w := w) (n := n) (limit := limit) (u := repetitions B.shrink demand)
    (t := Fintype.card B.Entry) B.shrink demand (sel m).val J.scratch
      (ShrinkMotifOrder.stateNumber X m).val (ShrinkCallHeader.cdBase X m J.arena J.older J.pitch)
  oldEnd : ∀ u, J.arena.base (J.nodes u) + J.arena.stride ≤ J.scratch.staging
  parentFit : (packet).Fits J.arena w n
  parentEnd : J.arena.base J.node + (packet).bits.length ≤ J.scratch.staging
  packets : ∀ priv, J.ChildWords priv n → (packet).Stored J.arena (DFS.scratch n priv) →
    J.Packets n priv

end Job

variable (u : PairExponents B.growthConstant) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
variable {start : ℕ → ℕ} (hs : PolynomiallyBounded start)
local notation "P" => initialPositions b
local notation "T" => blockCount (u.θ : ℝ)
local notation "degree" => slotDegree S
local notation "ports" => Fintype.card LeafStartup.ScalarPort

open Classical in
include hb hs in
/-- The packet bounds and constructor use the job's real old and new layer
bases and the worker's actual post-stack reserve. -/
theorem eventually_packets :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : T n * S.laneBits ≤ lanes) (R : Type*) [CommRing R] (f : B.Entry → R)
      (hf : B.IsSolution f),
      let initial := pairInput S labels hD
      let firstRow := endAddress (BlockProgram.layout B (start n) (P n) (T n))
      ∀ z : (B.execute f hf (T n) hT initial).Choices,
        let vs := executeLevels B f hf (T n) hT initial z
        let tags := selected B f hf (T n) hT initial z
        let rows := words B.recordLimit (selectedLayers B f hf (T n) hT initial z)
        let G := NativeFrame.regions degree n firstRow rows (Fintype.card B.Entry)
        let limit := mapBase G ports n + extent (P n * degree) n
        let w := wordBits b n
        ∀ (i : Fin vs.length) (j : Fin S.steps) {g : ℕ}
          (X : State (a j) (packingLaneBits (a j) g)) (sel : SelectedScore.Selection B X)
          (bits : List Bool), vs[i] = shrinkLevel B f hf j X sel bits →
          ∀ (m : X.packingData.Motif) (party : Fin 6) (startWord : Word w)
            (sp : ShrinkResidentSources.Bounds B j X startWord (P n) (T n) i.val)
            (old : ShrinkCallDemandCells.Old X (selectedLayout X B.shrink sel) m party)
            (parent : (X.shrinkNext B.shrink (S.shrink j) sel).network.Half
              (X.packingData.shrinkPartySite (selectedLayout X B.shrink sel) m party)),
            startWord.val = start n →
            let J := job B j X (S.shrink j) sel m party startWord (P n) (T n) i.val sp
              n (firstRow + rows) (layerBase B.recordLimit firstRow tags i.val)
                (layerBase B.recordLimit firstRow tags (i.val + 1)) old parent
            PacketSpace B j X sel m party J n limit := by
  filter_upwards [eventually_packed_occurrence B u b hb hs,
    ShrinkPackedRows.eventually_parent_width B u b hb] with n fits wide
  intro base lanes labels hD hT R _ f hf initial firstRow z vs tags rows G limit w i j g
    X sel bits atPass m party startWord sp old parent _ J
  let older := layerBase B.recordLimit firstRow tags i.val
  let later := layerBase B.recordLimit firstRow tags (i.val + 1)
  have size := wide labels hD hT R f hf z i j X sel bits atPass
  have fields := fits labels hD hT R f hf z i j X sel bits atPass m
  change SelectedFits X B sel m G b n limit older (B.recordLimit + 2) at fields
  have native : Fits (w := w) (n := n) (limit := limit)
      (u := repetitions B.shrink (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m))
      (t := Fintype.card B.Entry) B.shrink
      (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m) (sel m).val J.scratch
      (ShrinkMotifOrder.stateNumber X m).val
      (ShrinkCallHeader.cdBase X m J.arena J.older J.pitch) := by
    change Fits (w := w) (n := n) (limit := limit) (t := Fintype.card B.Entry)
      (u := repetitions B.shrink (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m))
      B.shrink _ (sel m).val (ShrinkCallHeader.scratch X (mapBase G ports n) (n ^ 2) G.histBase)
      _ (ShrinkCallHeader.cdBase X m G.arguments older (B.recordLimit + 2))
    rw [pow_two]
    exact fields
  have fit : mapBase G ports n < 2 ^ w := (Nat.le_add_right ..).trans_lt native.capacity.room
  have same : initial.positions = P n := pairInput_positions S labels hD
  have bounds := packet_bounds (X.shrinkNext B.shrink (S.shrink j) sel)
    (X.packingData.shrinkPartySite (selectedLayout X B.shrink sel) m party) parent
    J.nodes J.node degree (firstRow + rows) (Fintype.card B.Entry) J.scratch le_rfl (fun v ↦ by
      have row := ShrinkPackedRows.packed_shrink_address B f hf (T n) hT initial z
        (start n) i j X sel bits atPass v
      rw [same] at row
      exact row) (by
      have row := ShrinkPackedRows.packed_parent_address B f hf (T n) hT initial z
        (start n) i j X sel bits atPass
        (X.packingData.shrinkPartySite (selectedLayout X B.shrink sel) m party)
      rw [same] at row
      exact row) size.2 size.1 fit rfl
  refine ⟨native, bounds.1, bounds.2.1, bounds.2.2, ?_⟩
  intro priv children stored
  exact J.packets_of children bounds.1 bounds.2.1 stored bounds.2.2 native

end PairSimulation.ShrinkCanonicalJob

end VPVNP
end Computability
end OAI
