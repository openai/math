import OAI.Computability.VPVNP.CompressorShrinkEmitter
import OAI.Computability.VPVNP.CompressorRefreshEmitter
import OAI.Computability.VPVNP.CompressorScheduledPassCases

/-! # The complete two-case descriptor compiler at a common length

The finite calendar always selects either its specific shrinking worker or
the expander refresh worker. Both act on the actual selected graph and its
previously published records. The shared cost coefficient depends only on
the fixed templates. The threshold precedes the coefficient algebra,
workspace contents, selected graph and term choices.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.ScheduledTrace

open Compression BurstRAM DescriptorSpace CursorBounds PairSimulation.TraversalRoles Filter
open scoped Fin.CommRing

universe u v

variable {k : Type u} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- A fixed coefficient that covers every shrinking substep and the refresh of one block. -/
def descriptorRate := commonRawRate (ShrinkScheduledRun.fixedRate B) (RefreshEmit.rawRate B)

attribute [local irreducible] BlockProgram.script BlockProgram.layout BlockClock.small

/-- Above one length threshold, the actual selected pass runs in its allocated window over any coefficient ring. -/
theorem eventually_locatedRuns (factor : ℕ) (hb : 1 ≤ factor) : ∀ᶠ n : ℕ in atTop,
    ∀ {R : Type v} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
      (pub : Fin 11 → Word (wordBits factor n)) (blocks cap : ℕ) (initial : TaggedLayer)
      (frame : Fin 8 → Word (wordBits factor n)),
      let pos := initialPositions factor n
      let L := BlockProgram.layout B (pub 2).val pos blocks
      let small := BlockClock.small B factor n
      let A := BlockProgram.script B
      endAddress L < 2^wordBits factor n → small ≤ cap →
      Schedule.Online.Run.ControlBounds A.plan small (w := wordBits factor n) →
      LocatedRuns (CompiledResident.resident B f hf (pub 2) pos blocks n initial frame) pub (levelWords L)
        (directoryRows L) cap small (nativePassRate A (descriptorRate B)*pos) blocks pos n := by
  filter_upwards [ShrinkScheduledRun.eventually_emitAt.{u,v} B factor hb,RefreshPass.eventually_emitAt.{u,v} B factor hb]
    with n shrink refresh
  intro R inst f hf pub blocks cap initial frame pos L small A room clock control
  apply locatedRuns_of_passes
  · intro i g t X
    exact shrink f hf i X pub blocks t cap (RefreshEmit.rawRate B) initial frame room clock control
  · intro g t X
    exact refresh f hf X pub blocks t cap (ShrinkScheduledRun.fixedRate B) initial frame room clock control

end CompressorRecords.ScheduledTrace

end

end VPVNP
end Computability
end OAI
