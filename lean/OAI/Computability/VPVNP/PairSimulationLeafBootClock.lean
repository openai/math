import OAI.Computability.VPVNP.PairSimulationLeafBoot
import OAI.Computability.VPVNP.PairSimulationLeafIncidentTable

/-! # Uniform private clock for the complete auxiliary stack initializer -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafBoot

open BurstRAM CursorNetwork CursorRouting LeafStartup Filter

/-- One eventual bound applies to every input of the auxiliary initializer:
the cache and stride cost 89 ticks, the scalar pass costs at most n^14,
and the full incident copy costs at most n^5. -/
theorem eventually_ticks :
    ∀ᶠ n : ℕ in atTop, ∀ {A : PrimedInputRAM.Lengths} {a H s w d e : ℕ} [NeZero d]
      {Q : PrimedInputRAM.Layout A n a H w} (D : PrimedCounter.Data Q s) (hw : 2 ≤ w) (hc : 2^d*2^e<2^w)
      (v : Site d) (buf : Buffers d (2^e) w), ProcessorBudget n d e w → D.fuel ≤ n^10 →
      ticks D hw hc v buf ≤ n^15 := by
  filter_upwards [LeafPortTable.eventually_auxiliary_cost 52 34 scalarRows,eventually_ge_atTop 1024] with n hscalar hn
  intro A a H s w d e inst Q D hw hc v buf bud hf
  have hs := hscalar d e w (auxiliary D hw hc (0,v) buf) bud hf D.pub
  change scalarTicks D hw hc (0,v) buf ≤ n^14 at hs
  have hi := LeafIncidentMachine.ticks_le_of_budget v bud hn
  have hn' : 1 ≤ n := by omega
  have hp := Nat.pow_le_pow_right hn' (by decide : 5 ≤ 14)
  have h1 := Nat.one_le_pow 14 n hn'
  have hbig : 91*n^14 ≤ n^15 := by rw [pow_succ' n 14]; exact Nat.mul_le_mul_right _ (by omega)
  unfold ticks
  omega

end PairSimulation.LeafBoot

end VPVNP
end Computability
end OAI
