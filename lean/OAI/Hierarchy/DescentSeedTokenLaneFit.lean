import OAI.Hierarchy.DescentSeedTokenWidths
import OAI.Hierarchy.DescentSeedPitchFill

namespace OAI
/-! # Choosing a pitch that fits both sides of the original packed transpose -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSIMDLookup DescentCompiler.TerminalScale

theorem token_lane_fit (h words factor a b r : ℕ) (raw : 0 < a) (blocks : 0 < r)
    (space : 8*max (a*r) b ≤ h) (cpu : words ≤ factor*h) :
    let scale:=max (a*r) b
    let M:=lanes h (4*scale)
    0 < M ∧ M*r ≤ h ∧ a*r*M ≤ h/2 ∧ b*M ≤ h/2 ∧ words ≤ M*(16*factor*scale) :=by
  intro n M
  have p : 0 < n := (Nat.mul_pos raw blocks).trans_le (Nat.le_max_left ..)
  have cap : 2*(4*n) ≤ h:=by change 8*n ≤ h at space;omega
  have mPos:=(occupancy h (4*n) (by omega) cap).1
  have fits : (4*n)*M ≤ h/2 := by
    rw [Nat.mul_comm (4*n) M]
    exact lanes_fit h (4*n)
  have unit : n ≤ 4*n:=by omega
  have source : a*r*M ≤ h/2 :=
    (Nat.mul_le_mul_right _ ((Nat.le_max_left (a*r) b).trans unit)).trans fits
  have result : b*M ≤ h/2 :=(Nat.mul_le_mul_right _ ((Nat.le_max_right (a*r) b).trans unit)).trans fits
  have index : M*r ≤ h:=by
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ raw)).trans (source.trans (Nat.div_le_self ..))
  have filled:=pitch_fill h (4*n) words factor (by omega) cap cpu
  exact ⟨mPos,index,source,result,by simpa only [show 4*factor*(4*n)=16*factor*n by ring] using filled⟩

theorem token_epoch_room (h B α : ℕ) (positive : 0 < h) (late : 0 < Nat.log 2 h/(2*B))
    (bought : α+6 ≤ B) :
    16*scale (Nat.log 2 h/(2*B)) α ≤ h :=by
  let J:=Nat.log 2 h/(2*B)
  have large:=epoch_room h B (α+4) positive (by omega) late
  have four : 4 ≤ scale J 4:=by change 2^2 ≤ 2^(4*(J+1));apply Nat.pow_le_pow_right (by decide);omega
  rw [←scale_mul] at large
  nlinarith only [large,Nat.mul_le_mul_left (scale J α) four]

end Hierarchy.DescentDatedSeedStartup

end OAI
