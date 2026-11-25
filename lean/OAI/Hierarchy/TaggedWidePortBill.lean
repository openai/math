import OAI.Hierarchy.TaggedData
import OAI.Hierarchy.Catalyst
import OAI.Hierarchy.ProbeCoreReserve

namespace OAI
/-! # The external and recursive pin charges of the actual probe host -/

noncomputable section
namespace Hierarchy.Tagged
open ProbeStage ProbeStage.CoreBoard Catalyst
open scoped Classical BigOperators

/-- Both endpoints of every initially reserved core-column catalyst, every
payload pin and each exposed binary tag are charged for the native host. -/
theorem external_port_bill {h w d k R B : ℕ} (hd : 1≤d) (hw : h≤w) (cap : R≤B*w) :
    Fintype.card (Catalyst.Port (pins h w) (fun _ : Fin k=>Fintype.card (Columns h d)*R)) ≤
      (3+2*((2+2*(2*rounds d+1)*4^(rounds d+1))*k*B))*(2^h*w) := by
  have reserve := reserve_total_bound (k:=k) (h:=h) hd cap
  change Fintype.card (ReserveBits h d k R) ≤
    ((2+2*((permutationFabric h d).shapes.length)*4^(rounds d+1))*k*B)*(2^h*w) at reserve
  have length : (permutationFabric h d).shapes.length=2*rounds d+1 := template_length ..
  replace reserve : Fintype.card (ReserveBits h d k R) ≤
      ((2+2*(2*rounds d+1)*4^(rounds d+1))*k*B)*(2^h*w) :=
    reserve.trans_eq (by rw [length])
  change Fintype.card (Fin (pins h w) ⊕ (ReserveBits h d k R × Bool)) ≤ _
  rw [Fintype.card_sum,Fintype.card_fin,Fintype.card_prod,Fintype.card_bool]
  have p : pins h w ≤ 3*(2^h*w) := by
    unfold pins
    have := Nat.mul_le_mul_left (2^h) hw
    omega
  calc
    _ ≤ 3*(2^h*w)+((2+2*(2*rounds d+1)*4^(rounds d+1))*k*B)*(2^h*w)*2 :=
      Nat.add_le_add p (Nat.mul_le_mul_right 2 reserve)
    _ = _ := by ring

/-- Each installed slot exposes all three actual tagged fields irrespective
of whether the module is idle. The real slot budget has already counted
both copies of each installed module. -/
theorem bank_port_bill (h w copies parentWidth : ℕ) {R : ℝ}
    (height : h≤parentWidth) (width : w≤parentWidth) (slots : (copies:ℝ)*(2:ℝ)^h≤R) :
    (copies:ℝ)*pins h w ≤ 3*R*parentWidth := by
  have word : (2:ℝ)*w+h ≤ 3*(parentWidth:ℝ) := by
    exact_mod_cast (show 2*w+h ≤ 3*parentWidth by omega)
  calc
    (copies:ℝ)*pins h w = ((copies:ℝ)*(2:ℝ)^h)*(2*w+h) := by unfold pins; push_cast; ring
    _ ≤ R*(3*parentWidth) := mul_le_mul slots word (by positivity) ((by positivity : 0≤(copies:ℝ)*(2:ℝ)^h).trans slots)
    _ = _ := by ring

/-- Every control record exposes exactly three address-width fields,
and every one of the fresh readback gates can be accounted for here. -/
theorem control_port_bill (t h : ℕ) {R : ℝ} (height : t≤2*h) (rows : (2:ℝ)^t≤R) :
    (pins t t:ℝ) ≤ 6*R*h := by
  have one := bank_port_bill t t 1 (2*h) height height (R:=R) (by simpa using rows)
  calc
    _ ≤ 3*R*((2*h:ℕ):ℝ) := by simpa only [Nat.cast_one,one_mul] using one
    _ = _ := by push_cast; ring

end Hierarchy.Tagged

end
end OAI
