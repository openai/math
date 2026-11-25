import OAI.Hierarchy.DescentSIMDLookup
import OAI.ThreeFlat.Routing.CallBatches

namespace OAI
/-! # Total number of source-word probes across a change of packing -/
namespace Hierarchy.DescentSIMDLookup.Overlap
open ThreeFlat.Routing ThreeFlat.Routing.CallPool

private theorem ceiling_mul (n d : ℕ) : chunks n d*d≤n+d := by
  have h:=Nat.div_mul_le_self (n+d-1) d
  unfold chunks poolBatchCount
  omega

theorem probes {G A B : ℕ} (oldPos : 0<A) (newPos : 0<B) :
    chunks G B*min (chunks G A) (chunks B A+1)≤2*(chunks G A+chunks G B) := by
  let old:=chunks G A
  let new_:=chunks G B
  by_cases small : G≤B
  · have one : new_≤1:= by
      change (G+B-1)/B≤1
      have less : G+B-1<2*B:=by omega
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul newPos).mpr less)
    calc
      _ ≤ 1*old:=Nat.mul_le_mul one (min_le_left ..)
      _ ≤ _:=by dsimp [old];omega
  · have batch : new_*B≤2*G:=(ceiling_mul G B).trans (by omega)
    have stage : chunks B A*A≤B+A:=ceiling_mul B A
    have cover : G≤old*A:=by simpa [old,chunks,Nat.mul_comm] using count_le_batches_mul G A oldPos
    apply Nat.le_of_mul_le_mul_right ?_ oldPos
    calc
      _ ≤ (new_*(chunks B A+1))*A:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (min_le_right ..))
      _ = new_*(chunks B A*A+A):=by ring
      _ ≤ new_*(B+2*A):=Nat.mul_le_mul_left _ (by omega)
      _ = new_*B+2*(new_*A):=by ring
      _ ≤ 2*(old*A)+2*(new_*A):=Nat.add_le_add_right (batch.trans (Nat.mul_le_mul_left _ cover)) _
      _ = _ := by change _=2*(old+new_)*A;ring

theorem rounded (n : ℕ) : 2^Nat.clog 2 (n+1)≤2*(n+1) := by
  cases eqn:Nat.clog 2 (n+1) with
  | zero=>rw [pow_zero];omega
  | succ k=>
    have small : 2^k<n+1:=(Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mp (by omega)
    rw [pow_succ];omega

end Hierarchy.DescentSIMDLookup.Overlap

end OAI
