import OAI.Hierarchy.DescentOrdinarySharedLedger
import OAI.Hierarchy.DescentDonorExponentBounds

namespace OAI
/-! Choose the public skew and age denominator only after the coefficients of
the native ordinary/reset instructions and empty scan have been determined. -/
namespace Hierarchy.DescentCompiler.TerminalScale
open DescentSixParty Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- Uniform funding of the host and private-row terms entering the date ledger.
The payload-to-packed-width ratio is bought once for the entire original epoch. -/
theorem registered_rows (t f g reset coeff rate pack τ B : ℕ)
    (time : rate+2+pack ≤ τ) (pos : 0 < B)
    (age : rate+3+hostRate t reset*(t+1)+pack < B) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀M p : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
      let R:=coeff*scale J rate
      h ≤ p*scale J pack →
      ((S.length+1)*(R+1))*h ≤ p*2^(tail τ J) ∧
        (S.length+1)*(2^S.hostGain)^S.length*R*2^J ≤ p :=by
  let fixedCost:=(t+2)*(coeff+1)
  filter_upwards [AgeBound.payload_room (rate+3+hostRate t reset*(t+1)+pack) B age,
    eventually_ge_atTop (2^(fixedCost*(2*B)))] with h whole late
  intro J M p S R packing
  have enough:fixedCost ≤ J:=(Nat.le_div_iff_mul_le (by omega : 0 < 2*B)).mpr (Nat.le_log_of_pow_le (by decide) late)
  have unit:1 ≤ scale J rate:=Nat.two_pow_pos _
  have fixedBound:fixedCost ≤ scale J 1:=by
    change fixedCost ≤ 2^(1*(J+1))
    rw [Nat.one_mul]
    exact (enough.trans (Nat.le_succ J)).trans (Nat.lt_two_pow_self (n:=J+1)).le
  have jBound:J+1 ≤ scale J 1:=by simpa only [scale,Nat.one_mul] using (Nat.lt_two_pow_self (n:=J+1)).le
  have length:S.length+1 ≤ (t+2)*(J+1):=by change (t+1)*J+1 ≤ _;nlinarith
  have localCost : R+1 ≤ (coeff+1)*scale J rate:=by dsimp [R];rw [Nat.add_mul,Nat.one_mul];omega
  have matrix:(S.length+1)*(R+1) ≤ scale J (rate+2):=by
    calc
      _ ≤ ((t+2)*(J+1))*((coeff+1)*scale J rate):=Nat.mul_le_mul length localCost
      _ = (scale J rate*fixedCost)*(J+1):=by dsimp [fixedCost];ring
      _ ≤ (scale J rate*scale J 1)*scale J 1:=Nat.mul_le_mul (Nat.mul_le_mul_left _ fixedBound) jBound
      _ = _ :=by rw [scale_mul,scale_mul]
  have growth:(2^S.hostGain)^S.length ≤ scale J (hostRate t reset*(t+1)):=by
    change (2^(hostRate t reset))^((t+1)*J) ≤ 2^((hostRate t reset*(t+1))*(J+1))
    rw [←pow_mul,←Nat.mul_assoc]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.le_succ _))
  have tailRoom : scale J (rate+2+pack) ≤ 2^(tail τ J):=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ time)
  constructor
  · calc
      _ ≤ scale J (rate+2)*(p*scale J pack):=Nat.mul_le_mul matrix packing
      _ = p*(scale J (rate+2)*scale J pack):=by ring
      _ ≤ p*2^(tail τ J):=by rw [scale_mul];exact Nat.mul_le_mul_left p tailRoom
  · have scheduleRoom:(S.length+1)*(2^S.hostGain)^S.length*R*2^J ≤ scale J (rate+3+hostRate t reset*(t+1)):=by
      have period:2^J ≤ scale J 1:=by change 2^J ≤ 2^(1*(J+1));rw [Nat.one_mul];exact Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
      calc
        _ = (((S.length+1)*R)*(2^S.hostGain)^S.length)*2^J :=by ring
        _ ≤ (((S.length+1)*(R+1))*(2^S.hostGain)^S.length)*2^J := Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ _)))
        _ ≤ (scale J (rate+2)*scale J (hostRate t reset*(t+1)))*scale J 1:=
          Nat.mul_le_mul (Nat.mul_le_mul matrix growth) period
        _ = _ :=by rw [scale_mul,scale_mul];congr 1;omega
    change 2*scale J (rate+3+hostRate t reset*(t+1)+pack) ≤ h at whole
    have paid:scale J (rate+3+hostRate t reset*(t+1))*scale J pack ≤ p*scale J pack :=by
      rw [scale_mul]
      exact (show scale J (rate+3+hostRate t reset*(t+1)+pack) ≤ h by omega).trans packing
    exact scheduleRoom.trans (Nat.le_of_mul_le_mul_right paid (Nat.two_pow_pos _))

end Hierarchy.DescentCompiler.TerminalScale

end OAI
