import OAI.Hierarchy.DescentWideSeedCalendarFee
import OAI.Hierarchy.DescentStageLedger

namespace OAI
/-! # The first date pays the original packed ballots and the seed circuit -/
namespace Hierarchy.DescentWideSeedFlags
open DescentSeedRoot DescentCompiler DescentCompiler.TerminalScale DescentPackedEpochShelves
open DescentSixParty Filter
open scoped BigOperators
noncomputable section

/-- The same public allowance covers four gate charges and every actual
ordinal of the original profile selector. -/
theorem choice_bits (S : AtomSchedule) (C B h s Xsize : ℕ) (cut : 0 < B)
    (age : S.height=Nat.log 2 h/(2*B)) (width : s ≤ h) (size : Xsize+1 ≤ S.initialSites) :
    5*(80*S.copies*(Xsize+1)*(s.log2+1))+
        (S.length*S.batch)*DescentTerminalEpochBits.width C ≤ originalBill S C B h :=by
  let gain:=(S.rounds+1)*(S.hostGain+S.capGain+1)+11
  let D:=scale S.height gain
  let H:=S.hostSize 0*(S.groupCount 0*S.radix)
  have g:0 < gain:=by dsimp [gain];omega
  have factor:S.height+1 ≤ D:=(show S.height+1 ≤ 2^S.height from Nat.lt_two_pow_self).trans
    (Nat.pow_le_pow_right (by decide) (by have:=Nat.le_mul_of_pos_left (S.height+1) g;omega))
  have rows:H=S.initialSites*S.copies:=by
    dsimp [H,AtomSchedule.hostSize,AtomSchedule.groupCount,AtomSchedule.copies]
    rw [pow_succ S.radix S.length]
    simp only [Nat.mul_one]
    ring
  have sq : (Xsize+1)*S.copies ≤ H:=rows▸Nat.mul_le_mul_right _ size
  have digits:=seed_digits width cut
  rw [←age] at digits
  have dig : s.log2+1 ≤ 2*B*D:=digits.trans (Nat.mul_le_mul_left _ factor)
  have cost:=Nat.mul_le_mul sq dig
  have count : S.length*S.batch ≤ H*D:=selector_seats S (i:=0) (Nat.zero_le _) le_rfl
  have tiles:=Nat.mul_le_mul_right (DescentTerminalEpochBits.width C) count
  have unitFit:DescentTerminalEpochBits.width C ≤ unit C:=Nat.le_succ _
  have tilePrice:=Nat.mul_le_mul_left (H*D) unitFit
  change _ ≤ 328*S.initialSites*h+(1920*B+48*unit C)*H*D
  nlinarith only [cost,tiles,tilePrice,Nat.zero_le (S.initialSites*h),Nat.zero_le (H*(B*D)),Nat.zero_le (H*D*unit C)]

variable {F : Type} [Field F] (G : PoweredGadget F)
theorem original_calendar_price (t f g reset C τ B e : ℕ)
    (tailFit : 0+0+3+(e+5) ≤ τ) (positive : 0 < B)
    (widthFit : 2*((2+hostRate t reset*(t+1)+((t+1)*(hostRate t reset+capRate G t g+1)+11)+(0+1)+1)+5+e) ≤ B) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀ M q p : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
        0 < q → q ≤ scale J e → h ≤ 32*(q*p) →
        originalBill S C B h*2^J ≤ 2*(M*(S.copies*p)) := by
  let gain:=(t+1)*(hostRate t reset+capRate G t g+1)+11
  let c:=328+(1920*B+48*unit C)
  filter_upwards [calibration_at G t f g reset 0 gain e c 0 τ tailFit B positive widthFit] with h calibrated
  dsimp only
  intro M q p qpos qsize pack
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let coeff:=1920*B+48*unit C
  have high:328 ≤ scale J 0*(c*(tail τ J+1)^0):=by simp [scale,c]
  have low:scale J gain*coeff ≤ scale J gain*(c*(tail τ J+1)^0):=by
    simp only [pow_zero,Nat.mul_one]
    exact Nat.mul_le_mul_left _ (Nat.le_add_left ..)
  have price:=calibrated M q p 328 (scale J gain*coeff) qpos qsize pack high low (dateFee S C B h)
    (dateFee_room S C B h)
  change (∑i:Fin (S.length+1),dateFee S C B h i)*2^J ≤ 2*(M*(S.copies*p)) at price
  rwa [dateFee_sum] at price

end
end Hierarchy.DescentWideSeedFlags

end OAI
