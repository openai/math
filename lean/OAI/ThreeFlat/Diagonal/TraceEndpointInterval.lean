import OAI.ThreeFlat.Diagonal.TraceEndpointSlice

namespace OAI
/-! # Physical intervals and total demand of the genuinely free H endpoint pairs -/

namespace ThreeFlat.Diagonal.TraceSuffix
open scoped BigOperators

/-- The first free-pair ordinal beyond the first `lane` cursor buckets. -/
def boundary (T low lane : ℕ) := min T (lane*2^low)

theorem boundary_next (T low lane : ℕ) :
    boundary T low (lane+1)=boundary T low lane+pairs T low lane := by
  unfold boundary pairs
  rw [Nat.add_mul,Nat.one_mul]
  have positive : 0 < (2 : ℕ)^low := Nat.two_pow_pos _
  omega

theorem pairs_interval (T low lane : ℕ) :
    pairs T low lane=boundary T low (lane+1)-boundary T low lane := by
  rw [boundary_next]
  omega

theorem retained_interval (T low lane : ℕ) :
    retained T low lane=2*(boundary T low (lane+1)-boundary T low lane) := by
  rw [retained,pairs_interval]

theorem pairs_prefix (T low n : ℕ) :
    (∑ l : Fin n, pairs T low l.val)=boundary T low n := by
  induction n with
  | zero => simp [boundary]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc,boundary_next]
    change (∑ l : Fin n, pairs T low l.val)+pairs T low n=_
    rw [ih]

theorem retained_total {T low n : ℕ} (covers : T≤n*2^low) :
    (∑ l : Fin n, retained T low l.val)=2*T := by
  simp only [retained,←Finset.mul_sum,pairs_prefix,boundary,min_eq_left covers]


end ThreeFlat.Diagonal.TraceSuffix

end OAI
