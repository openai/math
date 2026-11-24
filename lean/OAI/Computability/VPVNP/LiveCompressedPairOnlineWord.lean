import OAI.Computability.VPVNP.LiveCompressedPairReachable
import OAI.Computability.VPVNP.LiveCompressedPairCursorStartup
import OAI.Computability.VPVNP.LiveCompressedPairStartupFootprint

/-! # Exact protected word readback after the eight setup calls and online stage -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair
open BurstRAM LiveStageLink CompressorRecords CompressorRecords.Schedule

variable {w d initial phases : ℕ} {C : Catalog d} {b : Bootstrap} {plan : Online.Config C initial phases}
  {terminal : PairTable} {pub : Fin 11 → Word w} {clock : ℕ} {m : Memory w}

private theorem completion_word {s : Stage} {entry : Memory w} (safe : Protected b plan terminal pub clock s entry)
    {a : ℕ} (keep : safe.word a) {st mem bs rs out}
    (run : Completion (components b plan terminal) next pub (PairTag.address pub) s (clockAt pub clock s) st mem bs rs out)
    (ready : safe.invariant st mem) (tag : mem (PairTag.address pub).val = tagWord w s) : out a = mem a := by
  induction run with
  | last call _ _ => exact keep _ _ _ _ ready tag call
  | more call cont _ _ ih =>
    obtain ⟨nextReady,nextTag⟩ := safe.frame _ _ _ _ _ ready tag call cont
    exact (ih nextReady nextTag).trans (keep _ _ _ _ ready tag call)

/-- Protect the readback across all actual source calls and the transfer
to the terminal tag. The ordinary path may have any finite length. -/
theorem Protected.onlinePost_word (safe : Protected b plan terminal pub clock Stage.online m)
    (p : StagePaths b plan terminal pub clock Stage.online m) (a : ℕ)
    (apart : a ≠ (PairTag.address pub).val) (keep : safe.word a)
    (tag : m (PairTag.address pub).val = tagWord w Stage.online) : onlinePost p a = m a := by
  have comp := completion_of_run (ordinaryRun p) p.property.choose_spec.2.1 p.property.choose_spec.2.2
  have effect := completion_word safe keep comp safe.ready tag
  change writeMemory (after m (eventLog (ordinaryReports p))) (PairTag.address pub) (tagWord w Stage.terminal) a = m a
  simpa only [writeMemory,ite_eq_right apart] using effect

/-- A completed genuine online run preserves the original prepared input
at every low cell protected by the selected source-frame invariant. -/
theorem Protected.after_startup_word (B n base : ℕ) (input : Memory w)
    (runs : TransferredStartup.Runs (bootstrapRows b initial phases) d (startupLayout b initial phases B n base)
      B n b.degreeBits b.lanesPerBlock b.steps pub (PairTag.address pub) input)
    (start : StartupResult b plan terminal pub B n base input clock)
    (safe : Protected b plan terminal pub clock Stage.online
      (after input (eventLog (cursorStartupLogs b pub B n base input initial phases d))))
    (p : StagePaths b plan terminal pub clock Stage.online
      (after input (eventLog (cursorStartupLogs b pub B n base input initial phases d))))
    (a : ℕ) (low : a < base) (apart : a ≠ (PairTag.address pub).val) (keep : safe.word a) :
    onlinePost p a = input a :=
  (safe.onlinePost_word p a apart keep start.tagged).trans (cursorStartup_after_below b pub B n base input runs a low apart)

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
