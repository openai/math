import OAI.Hierarchy.TraceRetainedScale
import OAI.ThreeFlat.Diagonal.PhysicalBlockCharge
import OAI.ThreeFlat.Diagonal.PhysicalNativeTicks

namespace OAI
/-! # Native clock of the actual repeated shrinking and refresh program -/

noncomputable section
namespace Hierarchy.TraceAdmission
open ThreeFlat Diagonal Diagonal.PhysicalStage
open TraceDistribution NavigationDirectory Computability.VPVNP.BurstRAM Filter

variable {F : Type} [Field F] (B : Block F)

theorem eventual_iteration_clock {u s : ℕ→ℕ} (scale : Scale u s) (K : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ (_fits : B.blockCharge*s w≤u w+1-w/2)
      (cur : Word (64*w)) (c : Cursor),
      let k:=u w+1-w/2
      let rem:=k-(B.repeat (s w)).charge
      let rows:=(B.prefix (.done _)).length
      let ticks:=Program.nativeTicks K cur (B.repeat (s w)) c rem k
      s w*(7+(rows*(rows*ticks)+1))+4 ≤ 2^(3*w/5) := by
  let rows := (B.prefix (.done _)).length
  filter_upwards [counted_room scale rows (B.nativeCoefficient K)] with w bound
  intro fit cur c k rem rs ticks
  have split : (B.repeat (s w)).charge+rem=k := by
    change (B.repeat (s w)).charge+(k-(B.repeat (s w)).charge)=k
    rw [B.charge_repeat]
    dsimp [k] at *
    omega
  exact bound ticks (B.native_cursor_time K (s w) cur c split)


end Hierarchy.TraceAdmission

end
end OAI
