import OAI.Hierarchy.DescentSeedNumberRates
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # Room for the short digits in the initial epoch -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty
theorem log_epoch (h B : ℕ) (pos : 0 < B) :
    Nat.log 2 h+1 ≤ (2*B)*scale (Nat.log 2 h/(2*B)) 1 :=by
  apply (log_height h B pos).trans
  apply Nat.mul_le_mul_left
  simpa only [scale,one_mul] using (Nat.lt_two_pow_self (n:=Nat.log 2 h/(2*B)+1)).le

theorem epoch_room (h B a : ℕ) (hpos : 0 < h) (wide : a+2 ≤ B) (old : 0 < Nat.log 2 h/(2*B)) :
    4*scale (Nat.log 2 h/(2*B)) a ≤ h :=by
  let J:=Nat.log 2 h/(2*B)
  have exp : 2+a*(J+1) ≤ J*(2*B) :=by
    have age : J+1 ≤ 2*J :=by dsimp only [J];omega
    have aa:=Nat.mul_le_mul_left a age
    have ab:=Nat.mul_le_mul_right J wide
    have one : 1 ≤ J:=old
    nlinarith only [aa,ab,one]
  have up:=exp.trans (Nat.div_mul_le_self (Nat.log 2 h) (2*B))
  calc
    4*scale J a=2^(2+a*(J+1)) :=by simp only [pow_add,scale];rfl
    _ ≤ 2^(Nat.log 2 h) :=Nat.pow_le_pow_right (by decide) up
    _ ≤ h:=Nat.pow_log_le_self 2 hpos.ne'

end Hierarchy.DescentDatedSeedStartup

end OAI
