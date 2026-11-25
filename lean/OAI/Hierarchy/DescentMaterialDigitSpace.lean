import OAI.Hierarchy.DescentDonorLaneNumbers
import OAI.Hierarchy.DescentPublicDegreeNumbers

namespace OAI
/-! # The authentic old donor register holds the full signed field alphabet -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentHostDegree DescentSharedCableNames DescentHaloWalkRAM

/-- Even at the first width, a real donor group carries 256 complete old ports
and eight measured quantities for each port. Its four-hop chart covers large degrees. -/
theorem material_digit_space (s : Shape) (k : ℕ) (blocks : s.blocks=2^k)
    (capacity : 256≤ s.cap) (digit : 9≤ s.widths) :
    1300+2100*logDegree s.degree+8*k+12*s.widths≤2*totalBits s := by
  let D:=s.degree
  let P:=breadth D
  have rankWidth : 0<Packed.bits P := by
    have live : 0<P:=by dsimp [P,breadth];positivity
    have data:=Nat.le_pow_clog (by decide : 1<2) (P+1)
    by_contra! zero
    have no : Nat.clog 2 (P+1)=0:=Nat.eq_zero_of_le_zero zero
    rw [no,pow_zero] at data
    omega
  have paths : P≤chartBits s := by
    change P≤Packed.bits P*P
    exact Nat.le_mul_of_pos_left P rankWidth
  have logarithm : logDegree D≤D+1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ,Nat.mul_comm (2^D)]
    exact Nat.mul_le_mul_left 2 Nat.lt_two_pow_self.le
  have degreeCharge : 1300+2100*logDegree D≤35000+P := by
    by_cases small : D<16
    · omega
    · have cube : 2100≤(D+1)^3 := by
        exact (by decide : 2100≤17^3).trans (Nat.pow_le_pow_left (by omega : 17≤D+1) _)
      have count:=Nat.mul_le_mul_right (D+1) cube
      change 1300+2100*logDegree D≤35000+(D+1)^4
      rw [pow_succ]
      omega
  have inWidth : 4096*s.widths*2^k≤2*freshBits s := by
    have portion:=Nat.mul_le_mul_left (2*s.widths*2^k*8) capacity
    simpa only [freshBits,blocks] using
      (show 4096*s.widths*2^k≤2*(s.widths*((2^k*s.cap)*8)) by
        calc
          _ = (2*s.widths*2^k*8)*256 := by ring
          _ ≤ _ :=portion
          _ = _ :=by ring)
  have elements : 1≤2^k:=Nat.two_pow_pos _
  have dw : s.widths≤ s.widths*2^k:=Nat.le_mul_of_pos_right _ elements
  have dk : k≤ s.widths*2^k:=Nat.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_left _ (by omega))
  rw [Nat.mul_assoc] at inWidth
  change 1300+2100*logDegree D+8*k+12*s.widths≤_
  unfold totalBits
  omega

end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
