import OAI.Computability.VPVNP.CompressorBlockClock
import OAI.Computability.VPVNP.LiveCompressedPairHandoff
import OAI.Computability.VPVNP.LiveCompressedPairSourceCaps

/-! # The block program's source clock within the live pair clock

The inner source reports run at the fixed block program's polylogarithmic
clock. The workspace frame needs twenty-four ticks per call, and the pair
transfer needs three further ticks on a terminating source report.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledTrace

open BurstRAM Compression Schedule CursorBounds LiveProgram Filter
variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Private clock left after the online dispatch and the twenty-four framing instructions. -/
def sourceCap {w : ℕ} (pub : Fin 11 → Word w) (clock : ℕ) :=
  CompressedPair.clockAt pub clock CompressedPair.Stage.online - 24

set_option exponentiation.threshold 10000 in
theorem pair_room {G : PairStages.Group} {w n small : ℕ} (pub : Fin 11 → Word w)
    (hn : 128 ≤ n) (clock : G.clock = n^10000) (size : small ≤ n^9999) :
    small+3 ≤ sourceCap pub (G.clockAt LiveProgram.Stage.pair) ∧
      sourceCap pub (G.clockAt LiveProgram.Stage.pair)+24 =
        CompressedPair.clockAt pub (G.clockAt LiveProgram.Stage.pair) CompressedPair.Stage.online := by
  have upper := CompressedPair.private_clock_room G hn clock
  have disp : (LiveStageLink.dispatchEvents (PairTag.address pub) CompressedPair.Stage.online).length = 20 := rfl
  unfold sourceCap CompressedPair.clockAt
  rw [disp]
  omega

set_option exponentiation.threshold 10000 in
/-- The same length threshold supplies the real smaller clock and the
three transfer ticks for every group and every eleven-word operand vector. -/
theorem eventually_clocks (addr : ℕ) (ha : 1 ≤ addr) :
    ∀ᶠ n : ℕ in atTop, let small := BlockClock.small B addr n
      let script := BlockProgram.script B
      InitialScriptPackets.budget script (BlockProgram.layout B 0 0 0) (S.degreeExponent 0) ≤ small ∧
      Online.Run.ControlBounds script.plan small (w := wordBits addr n) ∧
      ∀ (G : PairStages.Group) (pub : Fin 11 → Word (wordBits addr n)), G.clock = n^10000 →
        small+3 ≤ sourceCap pub (G.clockAt LiveProgram.Stage.pair) ∧
        sourceCap pub (G.clockAt LiveProgram.Stage.pair)+24 =
          CompressedPair.clockAt pub (G.clockAt LiveProgram.Stage.pair) CompressedPair.Stage.online := by
  filter_upwards [BlockClock.eventually_room B addr ha 0,eventually_ge_atTop 128] with n room hn
  intro small script
  exact ⟨(BlockClock.start B addr n 0 0 0).1,room.2 _ le_rfl,fun G pub clock =>
    pair_room pub hn clock ((by simpa using room.1 : small ≤ n).trans (Nat.le_self_pow (by decide) _))⟩

end CompressorRecords.ScheduledTrace

end VPVNP
end Computability
end OAI
