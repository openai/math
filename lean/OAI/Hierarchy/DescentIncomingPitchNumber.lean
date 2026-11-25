import OAI.Hierarchy.DescentDatedOrdinaryDimensions
import OAI.Hierarchy.DescentWalshPrecisionNumbers
import OAI.Hierarchy.DescentPackedWalshLanes
import OAI.Hierarchy.DescentRoundQuota
import OAI.Hierarchy.DescentResetDigits

namespace OAI
/-! # Calendar choice of the ordinary, reset or terminal incoming lane count -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentPackedWalsh DescentPacking.PackedMatch.Local.Stage
noncomputable section
variable (S:AtomSchedule) (k tail p f payload:ℕ) (ordinary:ℕ→Dated.Ordinary)
def resetCut (i:ℕ):ℕ:=
  let m:=S.groupWidth k tail i+k
  laneBits m payload (S.localWalshBits p m f (quota S.rounds))-k

def incoming (i:ℕ):ℕ:=
  if i<S.length then
    if i%(S.rounds+1)=S.rounds then 2^(resetCut S k tail p f payload i)
    else (ordinary i).lanesAt
  else S.groupCount S.length

theorem at_ordinary (e j:ℕ)(hj:j<S.rounds)(within:e*(S.rounds+1)+j<S.length):
    incoming S k tail p f payload ordinary (e*(S.rounds+1)+j)=(ordinary (e*(S.rounds+1)+j)).lanesAt:=by
  have rem:(e*(S.rounds+1)+j)%(S.rounds+1)=j:=by
    rw [Nat.mul_comm e,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (by omega)]
  simp only [incoming,ite_eq_left within,rem,ite_eq_right (Nat.ne_of_lt hj)]

theorem at_reset (e:ℕ)(within:e*(S.rounds+1)+S.rounds<S.length):
    incoming S k tail p f payload ordinary (e*(S.rounds+1)+S.rounds)=
      2^(resetCut S k tail p f payload (e*(S.rounds+1)+S.rounds)):=by
  have rem:(e*(S.rounds+1)+S.rounds)%(S.rounds+1)=S.rounds:=by
    rw [Nat.mul_comm e,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (Nat.lt_succ_self _)]
  simp only [incoming,ite_eq_left within,rem,ite_true]

theorem terminal :incoming S k tail p f payload ordinary S.length=S.groupCount S.length:=by simp [incoming]

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
