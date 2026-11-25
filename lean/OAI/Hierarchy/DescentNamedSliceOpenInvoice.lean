import OAI.Hierarchy.DescentTerminalSliceMachine
import OAI.Hierarchy.DescentResetRetainedCalendarWidths
import OAI.Hierarchy.DescentPreflightHostUnits
import OAI.Hierarchy.DescentPrivateGateScale
import OAI.Hierarchy.DescentTerminalScheduleScale

namespace OAI
/-! # Six original archive normalization passes on the calibrated open terminal host -/
namespace Hierarchy.DescentSixParty
open DescentTerminalPointerDigits DescentOperandStateBanks
open DescentCompiler DescentCompiler.TerminalScale DescentTerminalSliceShelf DescentStaticWordColumn ProtocolRAM DescentSIMDLookup
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F:Type} [Field F] (G:PoweredGadget F) (t J f g reset M τ drift:ℕ)
local notation "S" => stageNumbers G t J f g reset M (tail τ J)
local notation "k" => groupBits t J (S).hostGain (S).capGain (cutRate t f g)
local notation "κ" => groupRate G t f g reset
local notation "α" => 1+operandExponent G (stageNumbers G t 0 f g reset 0 0)
local notation "scan" => α+κ+4

theorem slice_pass_multiplier (late : drift+1≤ scale J 1) :
    ((2+3*(S).retainedArgumentsAt G drift)+1)*(2^k+1)≤ scale J scan := by
  have amount : (S).retainedArgumentsAt G drift≤ scale J α :=
    ((S).capacities_at_scale G drift 1 late).2
  have groups : 2^k≤ scale J κ := Nat.pow_le_pow_right (by decide) (groupBits_linear ..)
  have one : 1≤ scale J α := Nat.one_le_two_pow
  have two : 1≤ scale J κ := Nat.one_le_two_pow
  have pad : 12≤ scale J 4 := by
    apply Nat.le_trans (show 12≤2^4 by decide)
    apply Nat.pow_le_pow_right (by decide)
    omega
  calc
    _ ≤ (6*scale J α)*(2*scale J κ) := Nat.mul_le_mul (by omega) (by omega)
    _ = (scale J α*scale J κ)*12 := by ring
    _ ≤ (scale J α*scale J κ)*scale J 4 := Nat.mul_le_mul_left _ pad
    _ = _ := by rw [scale_mul,scale_mul]

variable (s h w E factor : ℕ) {L blocks digits:ℕ} {width:Fin 6→ℕ}
    (base:ℕ) (chart:Fin L→Fin blocks→Gather.Address)
    (write:(f:Fin 6)→(Fin L→Cell digits)→Cell (width f))
    (m:Memory w)
local notation "H_" => (S).hostSize (S).length
local notation "T" => 2^J
local notation "fee" => DescentTerminalSliceShelf.cost base chart H_ digits
local notation "machine" => DescentTerminalSliceShelf.program base chart write H_ w

include m in
theorem native_slices_open_price (late : drift+1≤ scale J 1)
    (reserve : localSocketRate G t g+scan≤τ)
    (large : 10≤h) (support : 2^h≤2*(M*(S).copies)) (power : T≤ s)
    (arch : w+1≤factor*h) (packed : h≤32*(2^Nat.clog 2 (NativeBranch.localLimit G S)*s))
    (positive : 0<H_) (columns : L≤2+3*(S).retainedArgumentsAt G drift) (banks : blocks≤2^k)
    (digitRoom : DescentTerminalPointerFrame.size L digits≤2*2^(h/2))
    (read : ∀j x,(chart j x).Fits base H_ w) (_off : 2^digits<2^w)
    (room : DescentTerminalSliceShelf.fence base L digits (blocks*H_)<2^w)
    (front back : Procedure w) (rest prior : ℕ)
    (before : (rest+7*names (front.seq back))*(w+1)*T≤prior*(((S).copies*s)*(M+T*E))) :
    (rest+fee+7*names ((front.seq machine).seq back))*(w+1)*T≤
      (prior+7*16384*(2*factor))*(((S).copies*s)*(M+T*E)) := by
  let fund:=((S).copies*s)*(M+T*E)
  have work : (L+1)*(blocks+1)≤ scale J scan :=
    (Nat.mul_le_mul (Nat.add_le_add_right columns 1) (Nat.add_le_add_right banks 1)).trans
      (slice_pass_multiplier G t J f g reset M τ drift late)
  have low:=DescentTerminalSliceShelf.invoice base chart write m read room positive digitRoom work
  have position:=preflight_host_units G t J f g reset M τ h s scan reserve packed
  have half : 2^(h/2)*h*T≤M*((S).copies*s) := by
    calc
      _ ≤ (M*(S).copies)*s := Nat.mul_le_mul (table_fund large support) power
      _ = _ := by ring
  have original : M*((S).copies*s)≤fund := by
    dsimp only [fund]
    rw [Nat.mul_add,Nat.mul_comm M]
    omega
  have resources : (2^(h/2)+H_*scale J scan)*h*T≤2*fund := by
    calc
      _ = 2^(h/2)*h*T+(H_*scale J scan)*h*T := by ring
      _ ≤ fund+fund := Nat.add_le_add (half.trans original) (position.trans original)
      _ = _ := by ring
  have weighted : (fee+7*names machine)*(w+1)*T≤(7*16384*(2*factor))*fund := calc
    _ ≤ (7*(16384*(2^(h/2)+H_*scale J scan)))*(factor*h)*T :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) arch)
    _ = (7*16384*factor)*((2^(h/2)+H_*scale J scan)*h*T) := by ring
    _ ≤ (7*16384*factor)*(2*fund) := Nat.mul_le_mul_left _ resources
    _ = _ := by ring
  rw [names_seq] at before
  simp only [names_seq]
  calc
    _ = (rest+7*(names front+names back))*(w+1)*T+(fee+7*names machine)*(w+1)*T := by ring
    _ ≤ _ := (Nat.add_le_add before weighted).trans_eq (by ring)


end
end Hierarchy.DescentSixParty

end OAI
