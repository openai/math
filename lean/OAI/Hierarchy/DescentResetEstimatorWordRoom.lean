import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI
/-! # Scalar capacities for the reset score, stencil header and actor address -/
namespace Hierarchy.DescentSixParty

/-- The data used in a reset estimator consist of its full actor axis and its two
Walsh axes. The header stores the dimension and the original census precision. -/
structure ResetEstimatorWords (hosts dim precision census degree w : ℕ) : Prop where
  score : 3*dim+(precision+Nat.clog 2 (hosts*(dim+1+degree)))+2≤w
  header : Nat.clog 2 (dim+2)+(dim+census)≤w
  host : hosts<2^w

theorem ResetEstimatorWords.of_sizes {hosts m b census D h w : ℕ}
    (sites : hosts≤2^(3*h)) (word : 8*b≤h/2) (contents : 3*m+2*census+1≤b)
    (deg : D≤h) (large : 3≤h) (bus : 9*h≤w) :
    ResetEstimatorWords hosts m b census D w :=by
  have dim : m≤h:=by omega
  have stripes : m+1+D≤2^(h+1):=by
    have growth : h<2^h:=Nat.lt_two_pow_self
    rw [pow_succ]
    omega
  have joint : Nat.clog 2 (hosts*(m+1+D))≤4*h+1:=by
    apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).2
    calc
      _ ≤ 2^(3*h)*2^(h+1):=Nat.mul_le_mul sites stripes
      _ = _:=by rw [←pow_add];congr 1; omega
  have depth : Nat.clog 2 (m+2)≤m+2:=Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  exact ⟨by omega,by omega,sites.trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) (by omega))⟩

end Hierarchy.DescentSixParty

end OAI
