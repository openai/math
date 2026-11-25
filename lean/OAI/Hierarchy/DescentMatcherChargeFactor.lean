import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # Full instruction text and execution time of the ordinary matcher -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill
open DescentCompiler.TerminalScale

def matchingConstant := 200000*24*8^4

theorem matcher_tariff_factor (ticks text extra w Hh HG ratio J labor amount : ℕ)
    (paid : (ticks+text+extra)*w ≤
      Hh*(scale J labor*(8*ratio*matchingConstant))+
      HG*(scale J (labor+amount)*(8*ratio*matchingConstant))) :
    (ticks+7*text)*w ≤ (Hh+HG)*(ratio*scale J (labor+amount+41)) :=by
  have one : 56*matchingConstant≤scale J 41 :=by
    apply (by decide : 56*matchingConstant≤2^41).trans
    exact Nat.pow_le_pow_right (by decide) (show 41≤41*(J+1) by omega)
  have raise : scale J labor≤scale J (labor+amount) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_add_right ..))
  have combined : scale J (labor+amount)*scale J 41=scale J (labor+amount+41) :=by
    unfold scale
    rw [Nat.add_mul (labor+amount) 41 (J+1),pow_add]
  have hardware : (ticks+7*text)*w≤7*((ticks+text+extra)*w) :=by
    rw [←Nat.mul_assoc]
    exact Nat.mul_le_mul_right w (by omega)
  calc
    (ticks+7*text)*w ≤ 7*(Hh*(scale J labor*(8*ratio*matchingConstant))+
        HG*(scale J (labor+amount)*(8*ratio*matchingConstant))) :=
      hardware.trans (Nat.mul_le_mul_left _ paid)
    _ ≤ 7*(Hh*(scale J (labor+amount)*(8*ratio*matchingConstant))+
        HG*(scale J (labor+amount)*(8*ratio*matchingConstant))) := by gcongr
    _ = (Hh+HG)*(ratio*(scale J (labor+amount)*(56*matchingConstant))) :=by ring
    _ ≤ (Hh+HG)*(ratio*(scale J (labor+amount)*scale J 41)) :=by gcongr
    _ = _ :=by rw [combined]

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill

end OAI
