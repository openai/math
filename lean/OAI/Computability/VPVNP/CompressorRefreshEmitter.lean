import OAI.Computability.VPVNP.CompressorRefreshPassRun
import OAI.Computability.VPVNP.CompressorCanonicalWorkerFit
import OAI.Computability.VPVNP.CompressorScheduledPassCases
import OAI.Computability.VPVNP.CompressorBlockClock

/-!
# A uniform native refresh emitter for the advised field

One input-length threshold suffices for every current graph, its true
partial history, every term, the coefficient interpretation, and the live
memory. The incoming and all selected outgoing widths satisfy the bounds
carried by the iterated compression. The emitted pass charges the actual
compiled refresh worker rate.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshPass

open Compression BlockPlanner DescriptorSpace Schedule CursorBounds Filter
open BurstRAM PairSimulation.TraversalRoles PairSimulation.LocalHistory ScheduledTrace
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

set_option maxHeartbeats 1400000 in
-- The port-motif choice and the scheduled pass share a dependent finite index.
theorem eventually_emitAt_capacity (factor : ℕ) (hb : 1 ≤ factor) : ∀ᶠ n : ℕ in atTop,
    ∀ positions ≤ initialPositions factor n, ∀ {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
      {g : ℕ} (X : State S.portExponent (S.portExponent + g))
      (pub : Fin 11 → Word (wordBits factor n)) (blocks round cap : ℕ)
      (shrinking : Fin S.steps → ℕ) (initial : TaggedLayer)
      (initialFrame : Fin 8 → Word (wordBits factor n)),
      let A := BlockProgram.script B
      let L := BlockProgram.layout B (pub 2).val positions blocks
      let small := BlockClock.small B factor n
      let rate := nativePassRate A (commonRawRate shrinking (RefreshEmit.rawRate B)) * positions
      let resident :=
        CompiledResident.resident B f hf (pub 2) positions blocks n initial initialFrame
      endAddress L < 2 ^ (wordBits factor n) → small ≤ cap →
      Online.Run.ControlBounds A.plan small (w := wordBits factor n) →
      EmitAt resident pub (levelWords L : Word (wordBits factor n)) (directoryRows L)
        cap small rate blocks positions n (PassOrigin.refresh X) ⟨round,.refresh⟩ := by
  have sizes := CursorRAM.eventual_word_room factor hb (CursorRAM.bounded_positions factor)
  have degrees := CursorRAM.eventual_word_room factor hb (PolynomiallyBounded.const (slotDegree S))
  have widths := CursorRAM.eventual_word_room factor hb
    ((PolynomiallyBounded.const (2 ^ S.portExponent)).mul PolynomiallyBounded.id)
  filter_upwards [sizes,degrees,widths,CanonicalWorker.eventually_fit B factor hb,
    PrefixLevelScale.eventually_refresh B factor hb] with n hpos hdeg hport hterm hnat
  intro positions available R _ f hf g X pub blocks round cap shrinking initial initialFrame A L small rate
    resident room clock little encode past m live index size width outputs ready
  let w := wordBits factor n
  let o := PassOrigin.refresh (B := B) (f := f) (hf := hf) X
  let termCap := SelectedTermWorker.clock B w
  let first := defaultSelection o
  have nativeFit := hnat R f hf X first width (outputs first).2
  have positive : 0 < termCap := by
    change 0 < (SelectedTerms.stepConstant B + 7) * (2 * w + 1)
    exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have big : Online.Run.ControlBounds A.plan cap (w := w) :=
    ⟨little.tags,little.calendar.trans clock,little.launch.trans clock⟩
  have depth : past.length = A.levelsPerBlock * round + S.steps := by
    rw [show A.levelsPerBlock = S.steps + 1 from rfl]
    simpa only [PassTimeline.Located.depth,Nat.mul_comm round] using index
  have fixed := BlockClock.fixed B factor n
  exact realize B f hf pub positions blocks round n X initial initialFrame termCap cap small
    shrinking encode past m live depth size room clock big little ready fixed.2.2.1
    (BlockClock.dynamic B factor n).2 ((size.trans available).trans_lt hpos) hdeg
    ((Nat.mul_le_mul_left (2 ^ S.portExponent) width).trans_lt hport)
    (hterm o (size.trans available) width).2.1 nativeFit.1 nativeFit.2.1 positive
    (fun c ↦ (hnat R f hf X c width (outputs c).2).2.2)

/-- The cursor uses its full initial position count. -/
theorem eventually_emitAt (factor : ℕ) (hb : 1 ≤ factor) : ∀ᶠ n : ℕ in atTop,
    ∀ {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
      {g : ℕ} (X : State S.portExponent (S.portExponent + g))
      (pub : Fin 11 → Word (wordBits factor n)) (blocks round cap : ℕ)
      (shrinking : Fin S.steps → ℕ) (initial : TaggedLayer)
      (initialFrame : Fin 8 → Word (wordBits factor n)),
      let positions := initialPositions factor n
      let A := BlockProgram.script B
      let L := BlockProgram.layout B (pub 2).val positions blocks
      let small := BlockClock.small B factor n
      let rate := nativePassRate A (commonRawRate shrinking (RefreshEmit.rawRate B)) * positions
      let resident :=
        CompiledResident.resident B f hf (pub 2) positions blocks n initial initialFrame
      endAddress L < 2 ^ (wordBits factor n) → small ≤ cap →
      Online.Run.ControlBounds A.plan small (w := wordBits factor n) →
      EmitAt resident pub (levelWords L : Word (wordBits factor n)) (directoryRows L)
        cap small rate blocks positions n (PassOrigin.refresh X) ⟨round,.refresh⟩ := by
  filter_upwards [eventually_emitAt_capacity B factor hb] with n run
  exact run (initialPositions factor n) le_rfl

end CompressorRecords.RefreshPass

end

end VPVNP
end Computability
end OAI
