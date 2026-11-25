import OAI.Hierarchy.DescentRegisteredInputNumbers
import OAI.Hierarchy.DescentRegisteredWidthCalendar

namespace OAI
/-! # One date rate for both physically copied predecessor fields -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook.MaterialProgram
noncomputable def inputReadRate {F : Type} [Field F] (G : PoweredGadget F) (t f g reset driftR base prev : ℕ) :=
  let zero:=stageNumbers G t 0 f g reset 0 0
  let q:=3+(driftR+operandExponent G zero)+groupRate G t f g reset
  let cur:=returnLaneRate G t f g reset (44*argumentDigitRate G t f g reset driftR base)
  18+2*(q+prev+cur+1)

theorem input_factors {J a b rows radix old working : ℕ} (work : working ≤ scale J a)
    (arg : rows ≤ scale J b) (rad : radix ≤ scale J b) (live : old ≤ scale J a) :
    retileFactor rows (max old working)+retileFactor radix (max old working) ≤ scale J (18+2*(b+a+1)) :=by
  let z:=scale J (b+a)
  have mono {r s : ℕ} (u : r≤ s) : scale J r ≤ scale J s:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ u)
  have small:=mono (show a≤b+a by omega)
  have orig:=mono (show b≤b+a by omega)
  have tariff:=Nat.add_le_add (retile_factor_le (arg.trans orig) ((max_le live work).trans small))
    (retile_factor_le (rad.trans orig) ((max_le live work).trans small))
  have one : z+1 ≤ scale J (b+a+1):=by
    have lo:1≤z:=Nat.two_pow_pos _
    have dbl : 2*z ≤ scale J (1+(b+a)):=
      (Nat.mul_le_mul_right z (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 1≤1*(J+1) by omega))).trans_eq
        (scale_mul J 1 (b+a))
    rw [Nat.add_comm 1 (b+a)] at dbl
    omega
  have c : 200000 ≤ scale J 18:=(by decide : 200000≤2^18).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  calc
    _ ≤ 200000*(z+1)^2:=tariff.trans_eq (by ring)
    _ ≤ scale J 18*(scale J (b+a+1))^2:=Nat.mul_le_mul c (Nat.pow_le_pow_left one 2)
    _ = _:=by unfold scale;rw [←pow_mul,←pow_add];congr 1;ring

end Hierarchy.DescentSixParty

end OAI
