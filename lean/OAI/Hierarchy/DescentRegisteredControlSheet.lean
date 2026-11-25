import OAI.Hierarchy.DescentRegisteredResetSample
import OAI.Hierarchy.DescentScheduledControlTariff

namespace OAI
/-! The selected control-register invoice at the genuine, archive-prefixed registered date. -/
namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset NativePitch Chronology Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (K : Parameters) (saving : ℕ)
local notation:max "first" a:arg J:arg τ:arg => (stageNumbers G K.t J K.f K.g K.reset (Sample.copies a) (tail τ J)).firstWidth G.b (Sample.p a)
local notation:max "grain" a:arg J:arg τ:arg => (stageNumbers G K.t J K.f K.g K.reset (Sample.copies a) (tail τ J)).grainAt G.b (Sample.p a) 0
local notation:max "cell" J:arg => groupBits K.t J (hostRate K.t K.reset) (capRate G K.t K.g) (cutRate K.t K.f K.g)

theorem control_sheet :
    ∃lead exponent share cutoff : ℕ,∀τ B,0 < τ → 0 < B → 2*τ+cutoff ≤ B →
    G.b ≤ 2^(capRate G K.t K.g) → ∀ᶠ h : ℕ in atTop,∀a : Sample G board op K τ B h,
    a.Geometry → a.ReachedAt →
    let J:=Nat.log 2 h/(2*B)
    a.hardware.inner.successor.controlRegisters.fee*a.w ≤ a.hostWork*(lead*scale J exponent)+
      a.groupWork*(lead*scale J exponent)+share*(a.copies/(2^J)^saving) := by
  obtain ⟨lead,exponent,late⟩:=scheduled_control_tariff G board K.t K.f K.g K.reset K.degree K.receiver K.ratio saving
  refine ⟨lead,exponent,1,0,?_⟩
  intro τ B _ den _ _
  filter_upwards [late op K.drift τ B den] with h current
  intro a g _ J
  let prev:=a.position.ports
  have received:=current a.copies a.age a.p a.w a.degreeLimit (first a J τ) (grain a J τ)
    prev.operandLanes prev.roleLanes a.ordinary prev.venue prev.io (prev.priorStart (cell J) a.position.floor)
    g.live g.input g.ambient g.bus g.hosts g.blocks g.degreeAt g.walsh g.root g.width
  simp only [one_mul]
  exact received

end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI
