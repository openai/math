import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Each whole addressable sheet fits inside its dyadic block rectangle -/
namespace Hierarchy.DescentDyadicSpan
theorem slice (k n:ℕ)(x:Fin (2^k)):
    x.val*n+2^Nat.clog 2 n≤2^Nat.clog 2 (2^k*n):=by
  by_cases empty:n=0
  · simp [empty]
  let b:=Nat.clog 2 (2^k*n)
  have kp:k≤b:=by
    have within:2^k≤2^k*n:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2^k) (by omega:1≤n)
    simpa only [Nat.clog_pow 2 k (by decide)] using Nat.clog_mono_right 2 within
  have total:2^k*n≤2^b:=Nat.le_pow_clog (by decide) _
  have cut:2^k*2^(b-k)=2^b:=by rw [←pow_add,Nat.add_sub_of_le kp]
  have envelope:2^k*n≤2^k*2^(b-k):=by rw [cut];exact total
  have limit:n≤2^(b-k):=Nat.le_of_mul_le_mul_left envelope (Nat.two_pow_pos _)
  have rounded:2^Nat.clog 2 n≤2^(b-k):=Nat.pow_le_pow_right (by decide) ((Nat.clog_le_iff_le_pow (by decide)).2 limit)
  calc
    x.val*n+2^Nat.clog 2 n≤x.val*2^(b-k)+2^(b-k):=Nat.add_le_add (Nat.mul_le_mul_left _ limit) rounded
    _=(x.val+1)*2^(b-k):=(Nat.succ_mul ..).symm
    _≤2^k*2^(b-k):=Nat.mul_le_mul_right _ x.isLt
    _=2^b:=cut

end Hierarchy.DescentDyadicSpan

end OAI
