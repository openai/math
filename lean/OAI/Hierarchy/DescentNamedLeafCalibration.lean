import OAI.Hierarchy.DescentNamedTerminalLeaf
import OAI.Hierarchy.DescentNativeSocketScale

namespace OAI
/-! # The same public split, socket count and residual bits as the native calibration -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F)
variable (t J f g resetRate M τ height : ℕ)
local notation "tailBits" => tail τ J
local notation "S" => stageNumbers G t J f g resetRate M tailBits
local notation "k" => groupBits t J (S).hostGain (S).capGain (cutRate t f g)
local notation "W" => NativeBranch.binLimit («k»:=k) S
local notation "j" => Nat.clog 2 (NativeBranch.localLimit G S)
local notation "U" => G.b^(t*J)*G.b
local notation "q" => 2^j*U
local notation "piece" => height/(16*(q*W))
local notation "p" => W*piece
local notation "a" => (S).groupWidth k tailBits 0+k
local notation "rest" => a-2*j
local notation "σ" => localSocketRate G t g
/-- The actual third-flight word fits one paid exterior packet of the compiled circuit. -/
theorem calibrated_public_word :
    2^j*(S).firstWidth G.b p=q*(W*piece) := by
  rw [AtomSchedule.firstWidth,AtomSchedule.grain_initial]
  change 2^j*(p*G.b^(t*J)*G.b)=(2^j*(G.b^(t*J)*G.b))*p
  ac_rfl

private abbrev leafSchedule := S
private abbrev leafGroupBits := k
private abbrev leafPayload := p

variable {cut n h C : ℕ}
variable (ordinary : OrdinaryRates G (leafSchedule G t J f g resetRate M τ)
  (leafGroupBits G t J f g resetRate M τ) cut)
variable (reset : ResetRates G (leafSchedule G t J f g resetRate M τ)
  (leafGroupBits G t J f g resetRate M τ) (atRound (leafSchedule G t J f g resetRate M τ).rounds)
  n h C f g cut (tail τ J))
variable (branch : G.b ≤ 2^(leafSchedule G t J f g resetRate M τ).capGain)
  (positive : 0 < leafPayload G t J f g resetRate M τ height) (room : 10*(X.size+1) ≤ M)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^(leafSchedule G t J f g resetRate M τ).rounds ≤ 1/2)
variable (c : (Epochs.finish G _ _ (normalized_epochs_issued_joint X G (leafSchedule G t J f g resetRate M τ)
  ordinary reset branch positive room shorten).choose).Choice)
variable (age : 0<J) (large : 2*localSocketRate G t g ≤ τ)

/-- At the calibrated input height all row widths, row counts, socket ceilings and
copy coordinates are public. The only choice below is the selected native history. -/
def calibratedLeaf (template : DescentTerminalCompiledPrefix.Shape) :=
  let cal:=native_socket_scale G t J f g resetRate M τ
  let coords : a=j+(j+rest) := by have lim:2*j≤a:=(cal.2.2.2.2.2.2.2 large).2;omega
  let enough : NativeBranch.localLimit G S ≤ q :=
    cal.2.1.trans (Nat.le_mul_of_pos_right _ cal.2.2.2.2.2.1)
  let fit : 0<q:=Nat.mul_pos (Nat.two_pow_pos _) cal.2.2.2.2.2.1
  purchasedLeaf X G S ordinary reset branch positive room shorten c
    (show (S).baseGroups=2^tailBits from rfl) coords age (Nat.le_refl _) enough fit template

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
