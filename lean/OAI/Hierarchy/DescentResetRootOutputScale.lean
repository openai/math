import OAI.Hierarchy.DescentNamedFundedScale
import OAI.Hierarchy.DescentRecordedRotorBatchRoom

namespace OAI
/-! # The reset output word bound from the public date and fixed menu -/
namespace Hierarchy.DescentDatedAddressBook.ResetMiddle
open DescentSixParty DescentCompiler DescentCompiler.TerminalScale DescentNamedFundedChart
open LinearAlgebra.SpectralBooks ThreeFlat
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d)

private theorem static_fit (J c : ℕ) : c ≤ scale J (Nat.clog 2 (c+1)) := by
  apply (Nat.le_succ c).trans ((Nat.le_pow_clog (by decide : 1 < 2) (c+1)).trans ?_)
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_mul_of_pos_right _ (Nat.succ_pos J))

private theorem grow {J a b : ℕ} (le : a≤b) : scale J a≤ scale J b :=
  Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_right _ le)

private theorem combine {J x y a b : ℕ} (left : x≤ scale J a) (right : y≤ scale J b) :
    x+y≤ scale J (max a b+1) := by
  let z:=scale J (max a b)
  have hx : x≤z := left.trans (grow (Nat.le_max_left ..))
  have hy : y≤z := right.trans (grow (Nat.le_max_right ..))
  have two : 2≤ scale J 1 := by
    unfold scale
    simpa using (Nat.pow_le_pow_right (n:=2) (by decide) (show 1≤J+1 by omega))
  calc x+y ≤ z*2 := by omega
       _ ≤ z*scale J 1 := Nat.mul_le_mul_left _ two
       _ = _ := scale_mul ..

/-- The coefficient for root headers, roles and matrices. Both the capacity prefix and
the number of layers enter through the public calendar. -/
def outputRate (Ht t f g reset C packet instruction : ℕ) :=
  let q:=8+((capPeriod G.b t g).map (·+1)).prod
  let a:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let v:=a+(1+q)
  max (Nat.clog 2 (rootCoefficient board Ht f C packet+1)+v)
    ((Nat.clog 2 ((instruction*(40*2^f+2))+1)+q)+Nat.clog 2 (G.b+1)*(t+1))+1

/-- This holds for every epoch, including the first, and for every potential successor
date even if no good base is occupied. It uses exactly the original selected capacity
prefix and the actual layer count times port batches. -/
theorem root_outputs_at (t J f g reset M tail age date Ht C packet instruction : ℕ) :
    let S:=stageNumbers G t J f g reset M tail
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    let cap:=((capCalendar G.b t g J).take age).prod*256
    rootWord board k Ht f cap C packet instruction
        (ClosedReset.calendarBatchCount S n packet f cap G.b date)
      ≤ scale J (outputRate G board Ht t f g reset C packet instruction) := by
  let S:=stageNumbers G t J f g reset M tail
  let cap:=((capCalendar G.b t g J).take age).prod*256
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let q:=8+((capPeriod G.b t g).map (·+1)).prod
  let a:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let v:=a+(1+q)
  let cb:=Nat.clog 2 (G.b+1)
  let ce:=rootCoefficient board Ht f C packet
  let cf:=instruction*(40*2^f+2)
  have cap0 : cap≤ scale J q := capPrefix G.b t g J age
  have low : 2^k≤ scale J a := Nat.pow_le_pow_right (by decide : 0 < 2) (groupBits_linear ..)
  have tw : 2≤ scale J 1 := by
    unfold scale
    simpa using (Nat.pow_le_pow_right (n:=2) (by decide) (show 1≤J+1 by omega))
  have pool : 2*cap≤ scale J (1+q) := (Nat.mul_le_mul tw cap0).trans_eq (scale_mul ..)
  have entire : 2^k*(2*cap)≤ scale J v := (Nat.mul_le_mul low pool).trans_eq (scale_mul ..)
  have sz : rootWord board k Ht f cap C packet instruction
      (ClosedReset.calendarBatchCount S n packet f cap G.b date) ≤
      ce*scale J v+instruction*(ClosedReset.calendarBatchCount S n packet f cap G.b date) :=
    rootWord_linear board k Ht f cap C packet instruction _ (scale J v) (Nat.two_pow_pos _) entire (low.trans (grow (by dsimp [v];omega)))
  have left : ce*scale J v≤ scale J (Nat.clog 2 (ce+1)+v) :=
    (Nat.mul_le_mul (static_fit J ce) (le_refl _)).trans_eq (scale_mul ..)
  have grains : ResetInput.calendarLanes S G.b date≤ scale J (cb*(t+1)) := by
    apply (S.grain_le_first G.b 1 date G.base_pos).trans
    rw [AtomSchedule.firstWidth,S.grain_initial,one_mul,←pow_succ]
    have width : G.b≤2^cb := (Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _)
    apply (Nat.pow_le_pow_left width _).trans
    rw [←pow_mul]
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    change cb*(t*J+1)≤cb*(t+1)*(J+1)
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith only [Nat.zero_le J,Nat.zero_le t])
  have layer : DescentRecordedRotorLayers.layers n packet f cap≤(40*2^f+2)*scale J q := by
    have ratio:=Nat.div_le_self (10*2^f*cap) (2^n*packet)
    have unit : 0<scale J q:=Nat.two_pow_pos _
    have scaledCap := Nat.mul_le_mul_left (10*2^f) cap0
    unfold DescentRecordedRotorLayers.layers
    calc
      _ ≤ 2*((10*2^f)*scale J q)+scale J q :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 (ratio.trans scaledCap)) unit
      _ = (20*2^f+1)*scale J q := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have roles : instruction*(ClosedReset.calendarBatchCount S n packet f cap G.b date) ≤
      scale J ((Nat.clog 2 (cf+1)+q)+cb*(t+1)) := by
    have l : instruction*DescentRecordedRotorLayers.layers n packet f cap≤cf*scale J q := by
      simpa only [cf,Nat.mul_assoc] using Nat.mul_le_mul_left instruction layer
    have l' := l.trans ((Nat.mul_le_mul (static_fit J cf) (le_refl (scale J q))).trans_eq (scale_mul ..))
    unfold ClosedReset.calendarBatchCount
    rw [←Nat.mul_assoc]
    exact (Nat.mul_le_mul l' grains).trans_eq (scale_mul ..)
  exact sz.trans (combine left roles)

end
end Hierarchy.DescentDatedAddressBook.ResetMiddle

end OAI
