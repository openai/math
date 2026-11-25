import OAI.Hierarchy.DescentNamedRetainedOperandBounds
import OAI.Hierarchy.DescentRegisteredPrimarySigned

namespace OAI
/-! Sizes of the retained operand rectangles, serials, and signed digits in the original reset. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentDatedAddressBook DescentOperandWidth
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule}
  {k age grain oldDegree wire hist n h C f g cut tail : ℕ}
  {incoming : Reached W G q ε S k age grain oldDegree wire hist}
  {ctl : ResetRates G S k oldDegree n h C f g cut tail} (B : ClosedReset incoming ctl)
  (p drift degree payload e previous M nextM packet : ℕ) (old : ResetOutput.Prior) (start w : ℕ)
local notation "v" => ResetOutput.fromBoard G S ctl.board k tail age p f g drift degree payload e previous M nextM
  C packet old start
local notation "chart" => (v).setup
local notation "r" => (chart).retained

structure OriginalPrimaryLimits : Prop where
  digitRoom : (r).bits*(chart).lanes ≤ w
  output : (r).bits ≤ (v).receiver.valueBits
  shelf : (r).donors < 2^(r).bits
  grainRoom : (chart).cable.units*B.next.placement.cap ≤ 2^(chart).cable.fieldBits
  alphabet : max (B.next.placement.degree+1) (B.next.placement.cap+1) ≤ 2^(v).receiver.signedBits
  newWidth : (r).nodes*(r).args ≤ 2^(r).bits
  oldWidth : (r).previousNodes*(r).previousArgs ≤ 2^(r).bits
  unitEq : (chart).cable.units=B.reset.unit/p
  donorEq : (chart).cable.donors=2^(S.groupWidth k tail age+k-B.terminals.commonDepth)
  rootCodec : DescentSignedCableCodec.width incoming.placement.degree incoming.placement.cap ≤ (v).middle.rootField
  positive : 1 < 2^(chart).fieldBits
  fieldRoom : (r).bits ≤ (chart).fieldBits
  chipRoom : DescentSignedCableCodec.width incoming.placement.degree incoming.placement.cap ≤ (chart).fieldBits

theorem original_primary_limits (recorded : B.Recorded p) (grainAt : grain=S.grainAt G.b p (age+1))
    (height : 0<S.height) (base : G.b≤2^S.capGain) (degreeAt : old.venue.degree=incoming.placement.degree)
    (capAt : incoming.placement.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)
    (previousNodes : old.nodes≤S.retainedNodes) (previousArgs : old.arguments≤S.retainedArgumentsAt G drift)
    (room : (v).finalEnd start<2^w) :
    OriginalPrimaryLimits B p drift degree payload e previous M nextM packet old start w := by
  obtain ⟨digitRoom,output,shelf,grainRoom,alphabet,newWidth,oldWidth⟩ :=
    named_retained_operand_bounds B p drift degree payload e previous M nextM packet old start w
      height base capAt previousNodes previousArgs room
  have fit := ResetInput.calendar_fit B.reset S G.b p (age+1) (B.unit.trans (congrArg (·*G.b) grainAt))
  have unitEq : (chart).cable.units=B.reset.unit/p := by
    change ResetInput.calendarLanes S G.b (age+1)=B.reset.unit/p
    rw [fit,Nat.mul_div_cancel _ recorded.positive]
  have donors : (chart).cable.donors=2^k :=
    (S.previousGeometry G k tail drift degree p age payload old.nodes old.arguments old.operandLanes
      ctl.base ctl.radix B.age).2.2.2.2.2.1
  have extent : S.groupWidth k tail age+k-B.terminals.commonDepth=k := by rw [B.commonDepth]; omega
  have rootCodec : DescentSignedCableCodec.width incoming.placement.degree incoming.placement.cap ≤ (v).middle.rootField := by
    rw [←degreeAt,capAt]
    exact signed_field_room old.venue.degree _ n k (GroupStage.depthBound old.venue.degree n f g)
  have fieldRoom : (r).bits ≤ (chart).fieldBits := Nat.le_max_left ..
  have two : 2 ≤ (r).bits :=
    (DescentOperandWidth.wide G S k tail drift degree).trans (Nat.le_max_left ..)
  have positive : 1 < 2^(chart).fieldBits :=
    (by decide : 1 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) (two.trans fieldRoom))
  exact ⟨digitRoom,output,shelf,grainRoom,alphabet,newWidth,oldWidth,unitEq,
    donors.trans (congrArg (fun t : ℕ => 2^t) extent.symm),rootCodec,positive,fieldRoom,
    named_retained_codec_room (ctl:=ctl) p drift degree payload e previous M nextM packet old start degreeAt capAt⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
