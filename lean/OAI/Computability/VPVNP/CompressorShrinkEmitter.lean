import OAI.Computability.VPVNP.CompressorShrinkPassRun
import OAI.Computability.VPVNP.CompressorShrinkCurrentBounds
import OAI.Computability.VPVNP.CompressorCanonicalWorkerFit
import OAI.Computability.VPVNP.CompressorShrinkTablesPhysical
import OAI.Computability.VPVNP.CompressorBlockClock

/-! # The common eventual shrinking emitter for every advised field

The arithmetic fitting threshold is selected before the old graph, model,
history, base address and branch. The resident supplies its native graph
representation. The single descriptor workspace bound covers the concrete
tables of every selected substep at this length.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.ShrinkScheduledRun

open Compression BlockPlanner DescriptorSpace Schedule CursorBounds Filter
open BurstRAM PairSimulation.TraversalRoles PairSimulation.LocalHistory ScheduledTrace
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

set_option maxHeartbeats 1800000 in
-- The proof specializes the worker and table bounds at each dependent pass input.
set_option maxRecDepth 6000 in
theorem eventually_emitAt (factor : ℕ) (hb : 1 ≤ factor) : ∀ᶠ n : ℕ in atTop,
    ∀ {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
      (i : Fin S.steps) {g : ℕ} (X : GreedyArena.ShrinkingState (ShrinkBlockInputs.a i) g)
      (pub : Fin 11 → Word (wordBits factor n)) (blocks round cap refreshRate : ℕ)
      (initial : TaggedLayer) (initialFrame : Fin 8 → Word (wordBits factor n)),
      let positions := initialPositions factor n
      let A := BlockProgram.script B
      let L := BlockProgram.layout B (pub 2).val positions blocks
      let small := BlockClock.small B factor n
      let rate := nativePassRate A (commonRawRate (fixedRate B) refreshRate) * positions
      let resident :=
        CompiledResident.resident B f hf (pub 2) positions blocks n initial initialFrame
      endAddress L < 2 ^ (wordBits factor n) → small ≤ cap →
      Online.Run.ControlBounds A.plan small (w := wordBits factor n) →
      EmitAt resident pub (levelWords L : Word (wordBits factor n)) (directoryRows L) cap small rate
        blocks positions n
        (PassOrigin.shrink i rfl X) ⟨round, .shrink i⟩ := by
  filter_upwards [ShrinkCurrentBranch.eventually_build B factor hb,
    CanonicalWorker.eventually_fit B factor hb,
    ShrinkOutput.eventually_tableArithmetic B factor hb] with n build fitted arith
  intro R _ f hf i g X pub blocks round cap refreshRate initial initialFrame positions A L
    small rate resident room clock little encode past m live index size width _ ready
  let src := old B i (pub 2).val positions blocks round live
  let dst := next B i (pub 2).val positions blocks round live
  let fuel := ShrinkBranch.prefixClock B factor n
  let o := (PassOrigin.shrink i rfl X : PassOrigin B f hf (B.shrinkPassAt f hf i rfl X))
  have ix : past.length = src.val := by
    simpa only [src, old, PassTimeline.Located.depth, Nat.mul_comm round] using index
  have current : CurrentGraph.Current L src.val X n m := ix ▸ ready.stored.1.2.1
  obtain ⟨prefixFit, ⟨common⟩⟩ := build f hf i X size width
    (pub 2).val blocks src dst m fuel current rfl room le_rfl
  have large : Online.Run.ControlBounds A.plan cap (w := wordBits factor n) :=
    ⟨little.tags, little.calendar.trans clock, little.launch.trans clock⟩
  have hfuel := (BlockClock.dynamic B factor n).1
  obtain ⟨fixed, _, _, dense⟩ := BlockClock.fixed B factor n
  exact realize B f hf i X pub positions blocks round n live initial initialFrame
    fuel cap small refreshRate past m encode common prefixFit ix size room
    (arith i X size width) (fitted o size width).2.1
    ((BlockClock.start B factor n (pub 2).val positions blocks).2 i) (dense i) hfuel fixed clock
    large little ready

end CompressorRecords.ShrinkScheduledRun

end

end VPVNP
end Computability
end OAI
