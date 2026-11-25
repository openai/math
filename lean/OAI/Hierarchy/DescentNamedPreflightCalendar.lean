import OAI.Hierarchy.DescentNamedPreflightOriginal
import OAI.Hierarchy.DescentTerminalScheduleScale

namespace OAI
/-! # Uniform register calibration on the actual outer height schedule -/
namespace Hierarchy.DescentSixParty.SeedNamed.PreflightCalendar
open DescentCompiler DescentCompiler.TerminalScale Filter
open scoped Classical
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F) (op:RotorSpec) (t f g reset τ B drift:ℕ)
def palette := 6*(terminalDegree G t f g reset+1)+19
def publicBits := localSocketRate G t g+Nat.clog 2 G.b*(t+1)
def primitive := max (DescentOperandWidth.rate G (stageNumbers G t 0 f g reset 0 0) 1 2) 4
def fieldExponent := Branch.shortExponent (palette G t f g reset) (groupRate G t f g reset) τ (publicBits G t g)
  (primitive G t f g reset) (Nat.clog 2 G.b*(t+1))
def scanExponent := Branch.scanExponent (groupRate G t f g reset) (primitive G t f g reset)
  (stageNumbers G t 0 f g reset 0 0).localCapacityExponent
def publicSlots (S:AtomSchedule) := 2^Nat.clog 2 (NativeBranch.localLimit G S)*(G.b^(S.rounds*S.height)*G.b)
variable (height:ℕ)
local notation "J" => Nat.log 2 height/(2*B)
local notation "κ" => groupRate G t f g reset
local notation "σ" => palette G t f g reset
local notation "ε" => publicBits G t g
local notation "a" => DescentOperandWidth.rate G (stageNumbers G t 0 f g reset 0 0) 1 2
local notation "E" => fieldExponent G t f g reset τ
/-- The mathematical dates are common to every reached choice and every input size. -/
structure Ready : Prop where
  positive : 0<J
  room : (2^J)^B≤height
  frozen : drift+1≤ scale J 1
  late : max (τ+κ*(t+2)) (max (a+1) (2*B))≤2^(J+1)
  scalar : ∀M p:ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
    p≤height → actualSpan G S op (publicSlots G S) p drift≤ scale J σ
  payer : ∀M:ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
    Nat.clog 2 (publicSlots G S+1)≤ scale J ε

theorem attained (positive:0<B) (rotor:G.b≤2^(capRate G t g)) (budget:2*(6*E+11)≤B) :
    ∀ᶠ height:ℕ in atTop,Ready G op t f g reset τ B drift height := by
  let threshold:=max (drift+1) (max (τ+κ*(t+2)) (max (a+1) (2*B)))
  filter_upwards [age_room B positive,eventually_late threshold B positive,
    issued_terminal_spans G op drift t f g reset τ B rotor positive] with h age late spans
  let j:=Nat.log 2 h/(2*B)
  change 0<j ∧ 32*(2^j)^B≤h at age
  change threshold≤j at late
  have maxLate:threshold≤2^(j+1):=late.trans ((by omega : j≤j+1).trans Nat.lt_two_pow_self.le)
  have hw:(2^j)^B≤h:=by omega
  have date:ε≤E:=by
    dsimp only [fieldExponent,Branch.shortExponent]
    omega
  have ey:ε*(j+1)≤j*B:=by
    have zz:=Nat.mul_le_mul_left ε (show j+1≤2*j by omega)
    have bound:=Nat.mul_le_mul_left j (show 2*ε≤B by omega)
    nlinarith only [zz,bound]
  have low:scale j ε≤h:=by
    apply le_trans _ hw;rw [←pow_mul];exact Nat.pow_le_pow_right (by decide) ey
  have slots (M:ℕ) : publicSlots G (stageNumbers G t j f g reset M (tail τ j))≤ scale j ε :=
    (native_socket_scale G t j f g reset M τ).2.2.2.2.2.2.1
  refine ⟨age.1,hw,?_,?_,?_,?_⟩
  · change drift+1≤2^(1*(j+1));rw [one_mul]
    exact (Nat.le_max_left ..).trans maxLate
  · exact (Nat.le_max_right ..).trans maxLate
  · intro M p
    dsimp only
    intro room
    exact (spans M p _ room ((slots M).trans low)).1
  · intro M
    exact (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=publicSlots G _))).trans (slots M)
end
end Hierarchy.DescentSixParty.SeedNamed.PreflightCalendar

end OAI
