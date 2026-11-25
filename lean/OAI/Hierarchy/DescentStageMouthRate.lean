import OAI.Hierarchy.DescentDatedMouthBounds
import OAI.Hierarchy.DescentStageOriginAperture

namespace OAI
/-! Stage-number specialization of the 20th-degree bound for the ordinary mouth.
The global field, drift, chart and degree constants are chosen before the height. -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale Chronology
noncomputable section
variable {F P : Type} [Field F] (G : PoweredGadget F)

def mouthRate (t f g reset D drift chart : ℕ) :=
  2048+originRate G t f g reset D+drift+chart+
    operandExponent G (stageNumbers G t 0 f g reset 0 0)

def mouthValues (oldDegree rdxBits oldCount capacity newCount receivers nargs nameWidth sizeWidth operandWidth : ℕ) : Fin 11→ℕ :=
  ![2048,oldDegree+1,2^rdxBits,oldCount,capacity,newCount,receivers,nargs,nameWidth,sizeWidth,operandWidth]

theorem stage_mouth_values (t f g reset D J M tail age drift driftRate chart : ℕ)
    (oldDegree rdxBits oldCount capacity newCount receivers nargs nameWidth sizeWidth operandWidth : ℕ) :
    let S:=stageNumbers G t J f g reset M tail
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    oldDegree ≤ D → rdxBits=k → oldCount ≤ S.retainedNodes → newCount ≤ S.retainedNodes →
    capacity ≤ ((capCalendar G.b t g J).take age).prod*256 →
    nargs ≤ S.retainedArgumentsAt G drift → drift+1 ≤ scale J driftRate →
    receivers ≤ scale J chart → nameWidth ≤ scale J chart →
    sizeWidth ≤ scale J chart → operandWidth ≤ scale J chart →
    ∀j,mouthValues oldDegree rdxBits oldCount capacity newCount receivers nargs nameWidth sizeWidth operandWidth j ≤ scale J (mouthRate G t f g reset D driftRate chart) :=by
  intro S k degree radix old next slot argumentCount drift_ lows labels sizes digits
  let a:=mouthRate G t f g reset D driftRate chart
  have mono {e : ℕ} (h : e ≤ a) : scale J e ≤ scale J a:=
    Nat.pow_le_pow_right (n:=2) (by decide) (Nat.mul_le_mul_right _ h)
  have above : a ≤ scale J a:=calc
    a ≤ a*(J+1):=Nat.le_mul_of_pos_right a (Nat.succ_pos J)
    _ ≤ 2^(a*(J+1)):=Nat.lt_two_pow_self.le
  have c : scale J chart ≤ scale J a:=mono (by dsimp [a,mouthRate];omega)
  have d : oldDegree+1 ≤ scale J a := ((Nat.succ_le_succ degree).trans
    (show D+1 ≤ a by dsimp [a,mouthRate,originRate];omega)).trans above
  have kb : k ≤ (1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)*(J+1):=groupBits_linear ..
  have rb : 2^rdxBits ≤ scale J a :=by
    rw [radix]
    exact (Nat.pow_le_pow_right (n:=2) (by decide) kb).trans (mono (by dsimp [a,mouthRate,originRate];omega))
  have nr : S.localTokenExponent=(stageNumbers G t 0 f g reset 0 0).localTokenExponent:=rfl
  have node : S.retainedNodes ≤ scale J a:=(S.capacities_scale G).1.trans (mono (by rw [nr];dsimp [a,mouthRate,originRate];omega))
  have cap:=slot.trans ((DescentNamedFundedChart.capPrefix G.b t g J age).trans (mono (by dsimp [a,mouthRate,originRate];omega)))
  have op : operandExponent G S=operandExponent G (stageNumbers G t 0 f g reset 0 0):=rfl
  have args:=argumentCount.trans ((S.capacities_at_scale G drift driftRate drift_).2.trans
    (mono (by rw [op];dsimp [a,mouthRate];omega)))
  have big : 2048 ≤ scale J a:=(show 2048 ≤ a by dsimp [a,mouthRate];omega).trans above
  intro j
  fin_cases j <;>
    first | exact big | exact d | exact rb | exact old.trans node | exact cap | exact next.trans node | exact lows.trans c |
            exact args | exact labels.trans c | exact sizes.trans c | exact digits.trans c

theorem stage_mouth_parameters (t f g reset D J M tail age drift driftRate chart : ℕ)
    (v : PhysicalOrdinary F P) :
    let S:=stageNumbers G t J f g reset M tail
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    v.area.D ≤ D → v.area.k=k → v.reference.oldNodes ≤ S.retainedNodes → v.resolver.nodes ≤ S.retainedNodes →
    v.reference.capacity ≤ ((capCalendar G.b t g J).take age).prod*256 →
    v.vector.operands ≤ S.retainedArgumentsAt G drift → drift+1 ≤ scale J driftRate →
    v.vector.lows ≤ scale J chart → v.bornBook.names ≤ scale J chart →
    v.bornBook.widths ≤ scale J chart → v.bornBook.bits ≤ scale J chart →
    ∀j,v.mouthParameters j ≤ scale J (mouthRate G t f g reset D driftRate chart) :=
  stage_mouth_values G t f g reset D J M tail age drift driftRate chart v.area.D v.area.k
    v.reference.oldNodes v.reference.capacity v.resolver.nodes v.vector.lows v.vector.operands
    v.bornBook.names v.bornBook.widths v.bornBook.bits

end
end Hierarchy.DescentSixParty

end OAI
