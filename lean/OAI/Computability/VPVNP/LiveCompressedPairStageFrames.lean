import OAI.Computability.VPVNP.LiveCompressedPairReindex
import OAI.Computability.VPVNP.LiveCompressedPairStartupFootprint

/-! # The outer live tag along actual compressed-pair continuations -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair.PhysicalStages

open BurstRAM CompressorRecords CompressorRecords.Schedule PairStages.Group.CompressedPaths

variable {d initial phases : ℕ} {C : Catalog d} {b : Bootstrap} {plan : Online.Config C initial phases}
    {finalTable : PairTable} {G : PairStages.Group} {B n base : ℕ} {m : Memory G.w}
    (S : PhysicalStages b plan finalTable G B n base m)

/-- The deterministic bootstrap and the two remaining selected stages
protect the outer live tag on every physically reachable continuing call. -/
theorem preservesOuterTag (fits : (Layout.shadow G.constants).eval G.g < 2^G.w) (before : G.addr.val < base)
    (runs : TransferredStartup.Runs (bootstrapRows b initial phases) d (startupLayout b initial phases B n base)
      B n b.degreeBits b.lanesPerBlock b.steps (publicWords G) (PairTag.address (publicWords G)) m)
    (online : S.onlineFrame.word G.addr.val) (terminal : ∀ p, (S.terminalFrame p).word G.addr.val) :
    PreservesTag G m := by
  apply preservesTag_of_protectsAddress
  unfold native
  rw [S.body]
  exact protectsAddress_startup b (publicWords G) B n base m plan finalTable (fuel G)
    ((by decide : 10 ≤ 21).trans G.tagFit) runs S.init G.addr.val before (outerTag_lt G fits).ne
    S.onlineFrame S.terminalFrame online terminal

end LiveProgram.CompressedPair.PhysicalStages

end VPVNP
end Computability
end OAI
