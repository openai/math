import OAI.Hierarchy.DescentPackedMatchShape
import OAI.Hierarchy.DescentPackedMatchProfileTable

namespace OAI
/-! # Polynomial local storage before the shared finite matching-table lookup -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSIMDLookup
noncomputable section

/-- The same public scale bounds block count, adjacency, port arity and profile bits.
The result covers the matching table as well as the two-word profile join. -/
theorem local_budget {r D p profile S : ℕ} (positive : 1≤S)
    (blocks : r≤S) (degree : D≤S) (ports : p≤S) (profiles : profile≤S) :
    let s:=shape r D p profile
    s.digit≤9*S^4 ∧ s.pairs≤2*S^5 ∧ ProfileTable.envelope s≤279*S^9 ∧
      s.digit*fields r D p≤27*S^6 := by
  let s:=shape r D p profile
  have ex {a b : ℕ} (h : a≤b) : S^a≤S^b := Nat.pow_le_pow_right (by omega) h
  have u2 : 1≤S^2 := (ex (a:=0) (by omega : 0≤2))
  have u4 : 1≤S^4 := (ex (a:=0) (by omega : 0≤4))
  have u5 : 1≤S^5 := (ex (a:=0) (by omega : 0≤5))
  have s2 : S≤S^2 := by simpa only [pow_one] using ex (by decide : 1≤2)
  have s4 : S≤S^4 := by simpa only [pow_one] using ex (by decide : 1≤4)
  have s5 : S≤S^5 := by simpa only [pow_one] using ex (by decide : 1≤5)
  have d2 : D*r≤S^2 := by simpa only [pow_two] using Nat.mul_le_mul degree blocks
  have rp : r*p≤S^2 := by simpa only [pow_two] using Nat.mul_le_mul blocks ports
  have bins : binCount r D≤2*S^2 := by dsimp [binCount];omega
  have count : entryCount r D p≤2*S^4 := by
    exact (Nat.mul_le_mul (Nat.mul_le_mul blocks bins) ports).trans_eq (by ring)
  have ds : digitWidth r D p profile≤9*S^4 := by
    unfold digitWidth
    apply max_le (by nlinarith only [profiles,s4])
    have bits : 2+entryCount r D p+binCount r D+(D+1)*r+r*p≤9*S^4 := by
      have small := ex (by decide : 2≤4)
      rw [Nat.succ_mul]
      omega
    exact (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)).trans bits
  have pairs : s.pairs≤2*S^5 := (Nat.mul_le_mul blocks count).trans_eq (by ring)
  have i5 : s.inFields≤17*S^5 := by
    change r+(binCount r D+(entryCount r D p*3+(entryCount r D p*3+s.pairs)))≤_
    have lo:=ex (by decide : 2≤5)
    have mid:=ex (by decide : 4≤5)
    omega
  have o5 : s.outFields≤25*S^5 := by change 1+s.pairs*12≤_;omega
  have inp : s.inputBits≤225*S^9 :=
    (Nat.mul_le_mul ds i5).trans (by nlinarith [show 0≤S^9 by positivity])
  have out : s.outputBits≤225*S^9 := (Nat.mul_le_mul ds o5).trans_eq (by ring)
  have eb : ProfileTable.envelope s≤279*S^9 := by
    have paid := Nat.mul_le_mul ds pairs
    change max s.inputBits s.outputBits+3*(s.digit*s.pairs)≤_
    have top := max_le inp out
    change digitWidth r D p profile*s.pairs≤_ at paid
    change max s.inputBits s.outputBits+3*(digitWidth r D p profile*s.pairs)≤_
    nlinarith only [paid,top]
  have f : fields r D p≤3*S^2 := by change r+(r*p+D*r)≤_;omega
  exact ⟨ds,pairs,eb,(Nat.mul_le_mul ds f).trans_eq (by ring)⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
