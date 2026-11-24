import OAI.Computability.VPVNP.CompressorBlockMetadataPackets
import OAI.Computability.VPVNP.CompressorBlockMetadataOperandReads
import OAI.Computability.VPVNP.CompressorShrinkForward

/-! # Installing the DFS metadata in shrinking and refresh substeps -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockMetadata

open BurstRAM Compression DescriptorSpace BlockPlanner Schedule SourceOnline
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {w : ℕ} (base : Word w) (positions blocks t cap : ℕ) (m : Memory w)
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "pub" => Ports.data pt
local notation "st" => (levelStart L (Script.levelsPerBlock scr*t) : Word w)

/-- Header fields published by the shrinking pass at this scheduled degree. -/
def shrinkFields (i : Fin S.steps) : Fields := .shrink (ShrinkBlockInputs.a i)
  (ShrinkBlockInputs.selectedInputs B (BlockProgram.geometry B) i (BlockProgram.arena B i.val 0))

/-- The metadata batch occupies group nine of the actual shrink. Its
report image fills the selected old and successor headers. -/
theorem shrink_group (i : Fin S.steps) (ht : t < blocks) (fit : endAddress L < 2^w)
    (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m ((pt).directory-1).val = (levelWords L : Word w)) (clock : scanCap scr 42 ≤ cap)
    (oldSites : ℕ) (old : (LevelFields.sites i.val).eval pub st m = (oldSites : Word w)) :
    ∃ ps : List (Packet scr w), Group scr L base cap
      (ShrinkForward.first B i t + ShrinkForward.visitsBefore B i 9) (directoryRows L) m ps ∧
      ps.map (fun p => p.stage.phase) = (BlockGroups.shrink B i 9).indices ∧
      Published B base positions blocks t i.val .shrink (shrinkFields B i) m oldSites
        (ps.flatMap SourceWalk.Packet.reports) := by
  let W := BlockGroups.shrink B i 9
  have offset : (scr).initial.length+t*(scr).block.length+W.before.length =
      ShrinkForward.first B i t+ShrinkForward.visitsBefore B i 9 := by
    rw [show W.before.length = _ from BlockGroups.shrink_offset B i 9]
    unfold ShrinkForward.first ShrinkForward.visitsBefore
    rw [show (9 : Fin 12).val = 9 by decide]
    omega
  rw [← offset]
  exact install B base positions blocks t i.val .shrink (shrinkFields B i) W cap m ht i.isLt.le fit
    rows pitch clock oldSites old (fun mem hr hs v hv => shrink_operand_reads B base positions blocks t i mem ht fit hr hs v hv)

/-- Header fields published when the port refresh reaches its metadata stage. -/
def refreshFields : Fields := .refresh S.steps (BlockProgram.arena B S.steps 4)

/-- Group four of the refresh carries the DFS row cursor across the
singleton-child placement and records the refresh role in the new header. -/
theorem refresh_group (ht : t < blocks) (fit : endAddress L < 2^w)
    (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m ((pt).directory-1).val = (levelWords L : Word w)) (clock : scanCap scr 42 ≤ cap)
    (oldSites : ℕ) (old : (LevelFields.sites S.steps).eval pub st m = (oldSites : Word w)) :
    let W := BlockGroups.refresh B 4
    ∃ ps : List (Packet scr w), Group scr L base cap
      ((scr).initial.length+t*(scr).block.length+W.before.length) (directoryRows L) m ps ∧
      ps.map (fun p => p.stage.phase) = W.indices ∧
      Published B base positions blocks t S.steps .refresh (refreshFields B) m oldSites
        (ps.flatMap SourceWalk.Packet.reports) := by
  intro W
  exact install B base positions blocks t S.steps .refresh (refreshFields B) W cap m ht le_rfl fit
    rows pitch clock oldSites old (fun mem hr hs v hv => refresh_operand_reads B base positions blocks t mem ht fit hr hs v hv)

end CompressorRecords.BlockMetadata

end

end VPVNP
end Computability
end OAI
