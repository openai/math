import OAI.Computability.VPVNP.CompressorBlockClock
import OAI.Computability.VPVNP.CompressorWorkspaceCore
import OAI.Computability.VPVNP.LiveCompressedPairOnlineRates

/-! # The literal block clock on chronological source reports -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM Compression CursorBounds CursorNetwork CompressorRecords Filter
open Schedule BranchSegments

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
local notation "scr" => BlockProgram.script B

/-- The literal small source clock controls every chronological report.
The total bound can have a different polylogarithmic exponent, including
zero. Both estimates are used before adding the six workspace reads. -/
theorem eventually_online_core_caps (u : PairExponents B.growthConstant) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    (rate q link : ℕ) :
    ∀ᶠ n : ℕ in atTop, let w := wordBits b n
      let small := BlockClock.small B b n
      small+link ≤ n ∧ (∀ cap, small ≤ cap → Online.Run.ControlBounds (scr).plan cap (w := w)) ∧
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1<virtualBits b n)
        (pub : Fin 11 → Word w) {st : Option (Word w)} {m : Memory w} {clock : ℕ}
        (segment : BranchSegments.Segment (OnlineWorkspace.program (scr).plan pub) clock st m)
        (source : OnlineWorkspace.Core scr pub segment small),
        RAMBuckets.cost Report.probes source.logs ≤ rate*(pairInput S labels hD).positions*(n.log2+1)^q →
        64*RAMBuckets.cost Report.probes source.logs ≤ processorCount b n*liveCapacity u n ∧
        ∀ r ∈ source.logs, r.probes+11 ≤ liveCapacity u n ∧ r.events.length+101 ≤ n := by
  obtain ⟨clockRate,bound⟩ := BlockClock.rate B b
  have bpos : 1 ≤ b := (by decide : 1 ≤ 5).trans ((le_max_right ..).trans hb)
  filter_upwards [BlockClock.eventually_room B b bpos link,
    eventually_online_of_local_rates B u b hb (max rate clockRate) (max q 4)] with n clock estimates
  intro w small
  refine ⟨clock.1,clock.2,?_⟩
  intro base lanes labels hD pub st m host segment source total
  have hp : 0 < n.log2+1 := Nat.succ_pos _
  apply estimates labels hD source.logs
  · exact total.trans (Nat.mul_le_mul (Nat.mul_le_mul_right _ (le_max_left ..))
      (Nat.pow_le_pow_right hp (le_max_left ..)))
  · intro r hr
    exact (source.ticks r hr).le.trans ((bound n).trans (Nat.mul_le_mul (le_max_right ..)
      (Nat.pow_le_pow_right hp (le_max_right ..))))

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
