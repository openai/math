import OAI.Hierarchy.DescentRoundQuota

namespace OAI
/-! The full register degree bound fits the reservation quota at the end of a period. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentHostDegree DescentBaseProfile
open scoped BigOperators

def maximumDegree (t : ℕ) := ∑ j : Fin t, atRound j.val

theorem maximumDegree_succ (t : ℕ) : maximumDegree (t+1) = maximumDegree t + atRound t := by
  unfold maximumDegree
  rw [Fin.sum_univ_castSucc]; rfl

private theorem ordinary_degree_double (d : ℕ) : 2*d ≤ ordinaryDegree d := by
  let win:=gap d+gainExponent 20 d
  have first : d+1 ≤ (d+1)*(win+1+2^win) := Nat.le_mul_of_pos_right _ (by positivity)
  have second : 2 ≤ 2^packExponent 20 d+2 := Nat.le_add_left 2 _
  calc
    2*d ≤ (d+1)*2 := by omega
    _ ≤ ((d+1)*(win+1+2^win))*(2^packExponent 20 d+2) := Nat.mul_le_mul first second
    _ ≤ ordinaryDegree d := Nat.le_self_pow (by decide : (10:ℕ)≠0) _

theorem maximumDegree_double (t : ℕ) : maximumDegree (t+1) ≤ 2*atRound t := by
  induction t with
  | zero => simp [maximumDegree,atRound]
  | succ t ih =>
    rw [maximumDegree_succ]
    have growth : 2*atRound t ≤ atRound (t+1) := ordinary_degree_double (atRound t)
    omega

theorem maximumDegree_quota (t : ℕ) : maximumDegree (t+1) ≤ quota t := by
  have exponent : 1 ≤ decayExponent (atRound t) := Nat.succ_pos _
  have two : 2 ≤ 2^decayExponent (atRound t) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) exponent
  calc
    maximumDegree (t+1) ≤ 2*atRound t := maximumDegree_double t
    _ = atRound t*2 := Nat.mul_comm ..
    _ ≤ atRound t*2^decayExponent (atRound t) := Nat.mul_le_mul_left _ two
    _ ≤ quota t := Nat.le_succ _

end Hierarchy.DescentSixParty.Chronology

end OAI
