import OAI.Computability.VPVNP.LiveCompressedPairReachable
import OAI.Computability.VPVNP.LiveDeterministicReachable
import OAI.Computability.VPVNP.LiveCompressedPairFrames

/-!
# Protecting live memory throughout the actual compressed pair

The eight forced startup tapes reach the online calendar. From that point,
every returning physical call preserves an outer address whenever its online
or terminal source invariant does. The terminal invariant starts on the
post-memory of the actual completed online branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.Schedule LiveStageLink

variable {w d initial phases : ℕ} {C : Catalog d} (b : Bootstrap) (plan : Online.Config C initial phases)
    (finalTable : PairTable) (pub : Fin 11 → Word w) (clock : ℕ) (fit : 10 ≤ 2^w)

/-- A source-table frame on genuinely reachable states supplies the second
address of the nested linker invariant, with unchanged bits and reports. -/
theorem Protected.ofSource_word (s : Stage) (m : Memory w) (a : ℕ)
    (inner : ∀ {st mem bits r st'}, SourceReachable b plan finalTable pub clock s m st mem →
      mem (PairTag.address pub).val = tagWord w s →
      execute (original b plan finalTable pub s) (clockAt pub clock s)
        ((original b plan finalTable pub s).start st) mem bits = some r → r.result = some st' →
      after mem r.events (PairTag.address pub).val = mem (PairTag.address pub).val)
    (source : ∀ {st mem bits r}, SourceReachable b plan finalTable pub clock s m st mem →
      mem (PairTag.address pub).val = tagWord w s →
      execute (original b plan finalTable pub s) (clockAt pub clock s)
        ((original b plan finalTable pub s).start st) mem bits = some r → after mem r.events a = mem a) :
    (Protected.ofSource b plan finalTable pub clock s m inner).word a := by
  intro st mem bits r reached tag run
  exact source reached tag ((execute_widen_start (stages b plan finalTable s).table
    (embedding b plan finalTable s) id pub (clockAt pub clock s) st mem bits).symm.trans run)

include fit in
theorem protectsAddress (m : Memory w) (logs : List (Report w))
    (startup : runSegment (program b plan finalTable pub) clock (some 0) m (List.replicate 8 []) = some logs)
    (cursor : endState (some 0) logs = some 0)
    (tag : (after m (eventLog logs)) (PairTag.address pub).val = tagWord w Stage.online)
    (online : Protected b plan finalTable pub clock Stage.online (after m (eventLog logs)))
    (terminal : ∀ p : StagePaths b plan finalTable pub clock Stage.online (after m (eventLog logs)),
      Protected b plan finalTable pub clock Stage.terminal (onlinePost p))
    (a : ℕ) (separate : a ≠ (PairTag.address pub).val)
    (bootFrame : ∀ r ∈ logs, ∀ entry, after entry r.events a = entry a)
    (onlineFrame : online.word a) (terminalFrame : ∀ p, (terminal p).word a) :
    ProtectsAddress (program b plan finalTable pub) clock 0 m a := by
  apply protects_after_empty_prefix startup cursor bootFrame
  apply ProtectsAddress.of_invariant (Phase online terminal) (Phase.start online terminal tag)
  exact fun active run cont => Phase.step online terminal fit a separate onlineFrame terminalFrame active run cont

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
