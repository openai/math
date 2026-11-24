import OAI.Computability.VPVNP.CompressorTransferredStartupFootprint
import OAI.Computability.VPVNP.LiveCompressedPairCursorStartup
import OAI.Computability.VPVNP.LiveCompressedPairProtection

/-!
# Address protection for the actual eight linked pair-startup reports

Replay the startup on the intermediate memories read by the native code. The
linker reads its own tag and appends its stage-transfer write to each report.
Every other cell below the descriptor workspace survives every returning call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.Schedule LiveStageLink
open scoped Fin.CommRing
open private startupStage from OAI.Computability.VPVNP.LiveCompressedPairCursorStartup

variable {w d initial phases : ℕ} {C : Catalog d}
variable (b : Bootstrap) (pub : Fin 11 → Word w) (B n base : ℕ) (m : Memory w)

/-- The frames of the eight source traces persist after their actual linker writes. -/
theorem cursorStartup_frame (runs : TransferredStartup.Runs (bootstrapRows b initial phases) d
    (startupLayout b initial phases B n base) B n b.degreeBits b.lanesPerBlock b.steps pub (PairTag.address pub) m)
    (x : ℕ) (hx : x < base) (ht : x ≠ (PairTag.address pub).val) :
    ReplayFrame x m (cursorStartupLogs b pub B n base m initial phases d) := by
  let t := startupTrace b pub B n base m initial phases d
  let tag := PairTag.address pub
  let entries := t.entry tag m
  apply ReplayFrame.ofFn entries (startupReport b pub B n base m initial phases d)
  · intro i
    change after (entries i.castSucc) (report pub (startupStage i.castSucc) (t.source i)).events = _
    rw [(report_effect pub _ _ _).2.2.2]
    have hclosed : (t.source i).result = none := TransferredStartup.source_closed ..
    have hn : next (startupStage i.castSucc) = some (startupStage i.succ) := by
      have h : (startupStage i.castSucc).val+1 < 10 := by change i.val+1 < 10; omega
      exact dite_eq_left h
    rw [hclosed,hn]
    exact (t.transfer tag m i).symm
  · intro i
    exact (runs.entry_below i.succ x hx ht).trans (runs.entry_below i.castSucc x hx ht).symm

/-- The linked startup's full event log leaves the original protected word
in the memory supplied to the online calendar. -/
theorem cursorStartup_after_below (runs : TransferredStartup.Runs (bootstrapRows b initial phases) d
    (startupLayout b initial phases B n base) B n b.degreeBits b.lanesPerBlock b.steps pub (PairTag.address pub) m)
    (x : ℕ) (hx : x < base) (ht : x ≠ (PairTag.address pub).val) :
    after m (eventLog (cursorStartupLogs b pub B n base m initial phases d)) x = m x :=
  ReplayFrame.after_eventLog _ _ (cursorStartup_frame b pub B n base m runs x hx ht)

variable (plan : Online.Config C initial phases) (finalTable : PairTable) (clock : ℕ)

/-- Protect an address on every continuing history of the native pair, using
the established frames of its online and final-stage calls. -/
theorem protectsAddress_startup (fit : 10 ≤ 2^w)
    (runs : TransferredStartup.Runs (bootstrapRows b initial phases) d (startupLayout b initial phases B n base)
      B n b.degreeBits b.lanesPerBlock b.steps pub (PairTag.address pub) m)
    (start : StartupResult b plan finalTable pub B n base m clock)
    (x : ℕ) (hx : x < base) (ht : x ≠ (PairTag.address pub).val)
    (online : Protected b plan finalTable pub clock Stage.online
      (after m (eventLog (cursorStartupLogs b pub B n base m initial phases d))))
    (terminal : ∀ p : StagePaths b plan finalTable pub clock Stage.online
      (after m (eventLog (cursorStartupLogs b pub B n base m initial phases d))),
      Protected b plan finalTable pub clock Stage.terminal (onlinePost p))
    (onlineFrame : online.word x) (terminalFrame : ∀ p, (terminal p).word x) :
    ProtectsAddress (program b plan finalTable pub) clock 0 m x := by
  apply protects_after_replayed_prefix start.executed start.cursor (cursorStartup_frame b pub B n base m runs x hx ht)
  apply ProtectsAddress.of_invariant (Phase online terminal) (Phase.start online terminal start.tagged)
  exact fun active run cont => Phase.step online terminal fit x ht onlineFrame terminalFrame active run cont

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
