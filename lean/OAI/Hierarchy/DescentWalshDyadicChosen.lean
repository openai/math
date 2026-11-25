import OAI.Hierarchy.DescentWalshLaneMedian
import OAI.Hierarchy.DescentWalshDyadicBudget
import OAI.Hierarchy.DescentPackedWalshPrice

namespace OAI
/-! # The fee of the installed power-of-two batch widths at every score precision -/

namespace Hierarchy.DescentWalshDyadicBudget
open ThreeFlat.Routing DescentPackedWalsh
open scoped BigOperators

/-- Failure of the next precision's table threshold forces one scalar in
both the old and new word, including the exact transition level. -/
theorem scalar_boundary (m h p : ℕ) (nonzero : 0<p) (late : h<8*(p+1)) :
    laneBits m h p=0 ∧ laneBits m h (p+1)=0 := by
  have old : h/(8*p)<2 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
  have new_:=Nat.div_eq_of_lt late
  simp [laneBits,Nat.log_of_lt old,new_]

theorem exact_batch (m l : ℕ) (below : l ≤ m) : poolBatchCount (2^m) (2^l)=2^(m-l) := by
  let P:=2^l
  have pos : 0<P := Nat.two_pow_pos _
  have product : 2^(m-l)*P=2^m := by rw [←pow_add,Nat.sub_add_cancel below]
  unfold poolBatchCount
  rw [←product]
  change (2^(m-l)*P+P-1)/P=_
  rw [show 2^(m-l)*P+P-1=2^(m-l)*P+(P-1) by omega,Nat.mul_comm (2^(m-l)) P,Nat.mul_add_div pos,Nat.div_eq_of_lt (by omega),Nat.add_zero]

theorem chosen_reduction (H m b W h K : ℕ) (scale : W≤K*h) (host : H≤2^W) (precision : b≤W+1) :
    (∑t ∈ Finset.range (Nat.clog 2 H),
      (4+90*sites H t*2^(m-laneBits m h (b+t+1)))*W)≤
      1004*(H+1)*W+12800*K*H*2^m*(b+1)+12800*K*2^m*(W+1)^2 := by
  let μ:=fun t=>2^(laneBits m h (b+t+1))
  apply le_trans _ (physical H m b W h K μ scale host precision (fun _ _=>Nat.two_pow_pos _)
    (fun t _=>laneBits_median m h (b+t+1) (by omega)))
  apply Finset.sum_le_sum
  intro t _
  unfold clock
  dsimp only [μ]
  have lane_le : laneBits m h (b+t+1) ≤ m := Nat.min_le_left _ _
  rw [exact_batch m (laneBits m h (b+t+1)) lane_le]
  gcongr; norm_num

theorem padded_le (H : ℕ) : 2^Nat.clog 2 H≤2*H+1 := by
  by_cases small : H≤1
  · interval_cases H <;> decide
  · have h:=Nat.pow_pred_clog_lt_self (by decide : 1<2) (by omega : 1<H)
    have e:=Nat.clog_pos (by decide : 1<2) (by omega : 1<H)
    cases eqn : Nat.clog 2 H with
    | zero=>omega
    | succ k=>
      rw [eqn] at h
      simp only [Nat.pred_succ] at h
      rw [pow_succ]
      omega

/-- An exactly balanced binary tree may have vacant leaves. Its entire
physical reduction is still linear in the original number of hosts. -/
theorem padded_reduction (H m b W h K : ℕ) (scale : W≤K*h) (host : H≤2^W) (precision : b≤W+1) :
    let e:=Nat.clog 2 H
    (∑t ∈ Finset.range e,(4+90*2^(e-(t+1))*2^(m-laneBits m h (b+t+1)))*W)≤
      2008*(H+1)*W+25600*K*(H+1)*2^m*(b+1)+12800*K*2^m*(W+1)^2 := by
  let e:=Nat.clog 2 H
  let n:=2^e
  have tree : n≤2^W:=Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow host)
  have capped : n≤2*H+1:=padded_le H
  have bill:=chosen_reduction n m b W h K scale tree precision
  have same : Nat.clog 2 n=e:=Nat.clog_pow 2 e (by decide)
  rw [same] at bill
  apply le_trans _ (le_trans bill ?_)
  · apply Finset.sum_le_sum
    intro t ht
    have lt:=Finset.mem_range.mp ht
    have count : sites n t=2^(e-(t+1)):=exact_batch e (t+1) lt
    rw [count]
  · have old := Nat.mul_le_mul_right W (Nat.mul_le_mul_left 1004 (Nat.add_le_add_right capped 1))
    have factors := Nat.mul_le_mul_right (2^m*(b+1)) (Nat.mul_le_mul_left (12800*K) capped)
    nlinarith only [old,factors,Nat.zero_le (K*2^m*(b+1))]

end Hierarchy.DescentWalshDyadicBudget

end OAI
