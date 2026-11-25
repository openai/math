import OAI.Hierarchy.DescentEarnedScalarArguments

namespace OAI
/-! # The terminal lookup tables in one purchased native word -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentResetGates DescentPrimitivePalette Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec)
variable (t f g reset drift W τ β h M : ℕ)
local notation "J" => Nat.log 2 h/(2*β)
local notation "sched" => stageNumbers G t J f g reset M (tail τ J)
local notation "groupLog" => groupBits t J (sched).hostGain (sched).capGain (cutRate t f g)
local notation "bins" => NativeBranch.binLimit (k:=groupLog) sched
local notation "j" => Nat.clog 2 (NativeBranch.localLimit G sched)
local notation "q" => 2^j*(G.b^(t*J)*G.b)
local notation "piece" => h/(16*(q*bins))
local notation "p" => bins*piece
local notation "s" => (sched).firstWidth G.b p
local notation "K" => NativeBranch.privateSlotCapacity G sched drift
local notation "tags" => DescentBundleTagKeys.capacity (colors G s ((sched).grainAt G.b p 0) op)
    (max 8 (2^(sched).capGain)) K p drift
local notation "groups" => (sched).groupCount (sched).length
local notation "V" => groups*2^groupLog
local notation "cap" => (capCalendar G.b (sched).rounds g (sched).height).prod*256
local notation "pageBits" => max 1 (V*actualSpan G sched op q p drift)
local notation "printBits" => 2+groups*max (max 1 (Nat.clog 2 (q+1))) (DescentSignedCableCodec.width 3 cap)

/-- Actual bounds of the three mounted tables and the scalar interpreter on the chosen word. -/
structure TerminalRoomAt : Prop where
  dense : DescentTerminalDenseWindow.formatBits q p+2*(q*p) ≤ h/2
  route : DescentTerminalBinFormat.controlBits bins q+
    DescentTerminalBinReaddress.sliceWidth bins q piece ≤ h/2
  scalar : DescentTerminalScalarHeader.range q tags K ((sched).epochPower^(sched).localTokenExponent) K p V+1 ≤ 2^(h/2)
  arguments : EarnedScalarArguments j s p q bins tags pageBits printBits h (W*h)

/-- The word multiplier precedes the tail, divisor, height, and input size. -/
theorem cofinal_terminal_room (branch : G.b≤2^(capRate G t g)) (word : 3≤W) :
    ∃β₀ : ℕ, ∀β≥β₀, ∀ᶠ h : ℕ in atTop, ∀M : ℕ,
      TerminalRoomAt G op t f g reset drift W τ β h M :=by
  let cohort:=2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))
  let routing:=2*((τ+groupRate G t f g reset+4)+(localSocketRate G t g+Nat.clog 2 G.b*(t+1))+2)
  refine ⟨max 1 (max cohort routing),?_⟩
  intro β paid
  have pos : 0<β := (le_max_left ..).trans paid
  have both : max cohort routing≤β := (le_max_right ..).trans paid
  have hc : cohort≤β := (le_max_left ..).trans both
  have hr : routing≤β := (le_max_right ..).trans both
  filter_upwards [terminal_format_calibration G op drift t f g reset τ β branch pos hc hr,
    earned_scalar_arguments G op drift t f g reset τ β branch pos hc hr] with h formats args
  intro M
  obtain ⟨dense,route,scalar⟩:=formats M
  exact ⟨dense,route,scalar,args M 0 0 (W*h) (Nat.mul_le_mul_right h word)⟩

end
end Hierarchy.DescentSixParty

end OAI
