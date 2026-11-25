import OAI.Hierarchy.DescentResetWalshScale
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # Public clock exponents for the re-packing and endpoint computation at every reset -/
namespace Hierarchy.DescentSixParty
open Filter DescentCompiler DescentCompiler.TerminalScale DescentPackedWalsh
variable {F : Type} [Field F] (G : PoweredGadget F)

def stencilRate (t f g reset : ℕ) :=
  (1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)+4

/-- The local capacity counts the suffix blocks processed by the endpoint evaluator. -/
def stencilCapacity (k b D n : ℕ) := 2^k+8*(b+D+n+7)

theorem stencil_capacity_at (t f g reset τ B K D n : ℕ) (den : 0<B) :
    ∀ᶠ h : ℕ in atTop, ∀M i p : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let m:=S.groupWidth k (tail τ J) i+k
      let b:=S.localWalshBits p m f K
      i≤S.length→p≤h→stencilCapacity k b D n+1≤ scale J (stencilRate G t f g reset) := by
  let C:=localCoefficient G t f g reset K τ
  let U:=8*(C*(2*B+1)^2+D+n+8)+1
  filter_upwards [eventually_late U B den] with h late
  intro M i p
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let m:=S.groupWidth k (tail τ J) i+k
  let b:=S.localWalshBits p m f K
  let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  change i ≤ S.length → p ≤ h → stencilCapacity k b D n + 1 ≤ scale J (stencilRate G t f g reset)
  intro date dataSize
  have jL:J≤Nat.log 2 h:=Nat.div_le_self ..
  have span : tail τ J≤τ*(Nat.log 2 h+1)^2:=Nat.mul_le_mul_left _ ((Nat.succ_le_succ jL).trans (by nlinarith))
  have actual:b≤C*(Nat.log 2 h+1)^2:=actual_width G t J f g reset M (tail τ J) i h p K τ dataSize jL span date
  have floor : Nat.log 2 h+1≤(2*B+1)*(J+1):=by
    have rem:=Nat.mod_lt (Nat.log 2 h) (show 0<2*B by omega)
    have eqn:=Nat.mod_add_div (Nat.log 2 h) (2*B)
    change Nat.log 2 h%(2*B)+2*B*J=Nat.log 2 h at eqn
    nlinarith only [eqn,rem]
  have bnd:b≤C*(2*B+1)^2*(J+1)^2:=by
    have r:=actual.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left floor 2))
    rwa [mul_pow,←Nat.mul_assoc] at r
  have one : 1 ≤ (J+1)^2 := by
    simpa only [one_pow] using Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.zero_le J)) 2
  have cst:8*(b+D+n+7)+1≤U*(J+1)^2:=by
    have left:=Nat.mul_le_mul_left (8*(D+n+8)+1) one
    dsimp [U]
    nlinarith only [bnd,left]
  have jpow:J+1≤2^(J+1):=Nat.lt_two_pow_self.le
  have coeff:U≤2^(J+1):=late.trans (by omega)
  have cub:U*(J+1)^2≤2^(3*(J+1)):=calc
    _ ≤ 2^(J+1)*(2^(J+1))^2:=Nat.mul_le_mul coeff (Nat.pow_le_pow_left jpow 2)
    _ = _:=by rw [←pow_mul,←pow_add];congr 1;omega
  have kin:k≤κ*(J+1):=groupBits_linear t J S.hostGain S.capGain (cutRate t f g)
  let T:=2^((κ+3)*(J+1))
  have kpart:2^k≤T:=Nat.pow_le_pow_right (by decide) (kin.trans (by nlinarith))
  have bpart:8*(b+D+n+7)+1≤T:=(cst.trans cub).trans (Nat.pow_le_pow_right (by decide) (by nlinarith))
  change stencilCapacity k b D n+1≤2^((κ+4)*(J+1))
  calc
    _ ≤ 2*T:=by unfold stencilCapacity;omega
    _ = 2^((κ+3)*(J+1)+1):=by simp only [T,pow_succ,Nat.mul_comm]
    _ ≤ _:=Nat.pow_le_pow_right (by decide) (by nlinarith)

/-- The exponent is fixed with the gadget, before the calendar tail and logarithmic age denominator. -/
theorem stencil_width_at (rate B : ℕ) (den : 0<B) (bought : 2*(3*rate+1)≤B) :
    ∀ᶠ h : ℕ in atTop,∀a : ℕ, let J:=Nat.log 2 h/(2*B)
      a+1≤ scale J rate→4*(30*(a+1)^3)≤h := by
  filter_upwards [age_room B den,eventually_late 120 B den] with h room late
  intro a J cap
  have cst:120≤2^(J+1):=late.trans ((Nat.le_succ J).trans (Nat.lt_two_pow_self.le))
  have v:4*(30*(a+1)^3)≤2^((3*rate+1)*(J+1)):=calc
    _ = 120*(a+1)^3:=by ring
    _ ≤ 2^(J+1)*(2^(rate*(J+1)))^3:=Nat.mul_le_mul cst (Nat.pow_le_pow_left cap 3)
    _ = _:=by rw [←pow_mul,←pow_add];congr 1;ring
  have one:0<J:=room.1
  have exp:(3*rate+1)*(J+1)≤J*B:=by
    have a:=Nat.mul_le_mul_left (3*rate+1) (by omega : J+1≤2*J)
    have b:=Nat.mul_le_mul_left J bought
    nlinarith only [a,b]
  have total : (2^J)^B ≤ h :=
    (Nat.le_mul_of_pos_left _ (by decide : 0 < 32)).trans room.2
  exact v.trans <| (Nat.pow_le_pow_right (by decide) exp).trans (by rwa [pow_mul])

end Hierarchy.DescentSixParty

end OAI
