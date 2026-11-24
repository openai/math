import OAI.Computability.VPVNP.LiveProgramCompressedPair
import OAI.Computability.VPVNP.PairTerminalVertexBank
import OAI.Computability.VPVNP.PairShrinkVertexImage
import OAI.Computability.VPVNP.PairRefreshVertexRun
import OAI.Computability.VPVNP.PaperPairParameters

/-! # The compressed-pair table fixed before the diagonal length

The online stage and terminal refresh use the same fixed refresh record
width and tie order. Both terminal map roles write into the same suffix
of the live histogram. The outer linker installs these instructions once,
before the scalar model, group headers, and selected compression branches.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace LiveProgram.CompressedPair

open Compression CompressorRecords PairSimulation CursorBounds CursorNetwork BurstRAM

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  (u : PairExponents B.growthConstant) (c : Constants)
  (labels : c.motifLabels = Fintype.card B.Entry)

/-- Compile the exact block calendar ratio and the physical descriptor shape. -/
def paperBootstrap : Bootstrap where
  shape := BlockProgram.allocationShape B
  degreeBits := S.degreeExponent 0
  lanesPerBlock := S.laneBits
  steps := S.steps
  numerator := (blockRatio u).num
  denominator := (blockRatio u).den

/-- Ordinal of a parameter in the suffix of the live counter bank. -/
def entryOrdinal : B.Entry ≃ Fin c.motifLabels :=
  (Fintype.equivFin B.Entry).trans (finCongr labels).symm

/-- The installed shrinking role counts occurrences in the live parameter order. -/
def shrinkRole : VertexImage.Segment := ShrinkVertexImage.shrinkSegment B (entryOrdinal B c labels)

/-- The installed refresh role uses the same tie order and record stride as the descriptor writer. -/
def refreshRole : VertexImage.Segment := RefreshVertex.refreshSegment B (RefreshBlockPlan.order B)
  (RefreshBlockPlan.shape B).stride (entryOrdinal B c labels)

/-- The actual geometry, root gather, cursor leaf and both map roles. The
geometry computes the live bucket from the same ratio as the outer program. -/
def paperSegments := TerminalProgram.installedSegments c S (liveRatio u).num (liveRatio u).den
  (shrinkRole B c labels) (refreshRole B c labels)

/-- The five linked terminal worker stages of the fixed compressed pair. -/
def paperTerminal : PairTable := TerminalProgram.installedTable B c (liveRatio u).num (liveRatio u).den
  (shrinkRole B c labels) (refreshRole B c labels)

/-- The complete eleven-operand pair subroutine, independent of the input length. -/
def paperTable : PairTable :=
  pairTable (paperBootstrap B u) (BlockProgram.script B).plan (paperTerminal B u c labels)

theorem paper_terminal_rows (base positions blocks : ℕ) :
    TerminalProgram.table (BlockProgram.layout B base positions blocks).shape B.recordLimit
      (paperSegments B u c labels) = paperTerminal B u c labels :=
  TerminalProgram.installed_at_layout ..

theorem paper_block_count (n : ℕ) :
    roundedDown (paperBootstrap B u).numerator (paperBootstrap B u).denominator n =
      blockCount (u.θ : ℝ) n :=
  blockRatio_floor u n

end LiveProgram.CompressedPair

end

end VPVNP
end Computability
end OAI
