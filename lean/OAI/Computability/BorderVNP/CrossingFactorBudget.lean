import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! # Polynomial resource bounds for the signed crossing queries

The finite mode checker is compiled with polynomial gate and witness bounds in
the cutoff and homogeneous-slice weight. Its wrapper translates the exposed
one-hot labels to occupation masks. A single polynomial in the wire alphabet
bounds every stage of the iterated crossing.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

/-- The label and padding logic around a local mode checker preserves a uniform polynomial
bound on both the number of private choices and the number of Boolean gates. -/
theorem factorChecker_budget {q H E W gates guesses size : ℕ} (hw : W ≤ 2*H)
    (hg : gates ≤ (E+H+W+2)^100) (hu : guesses ≤ (E+H+W+2)^100)
    (hs : size ≤ gates + (W+3*(E+H)+guesses)*(2*q+1) + 2*(2*W+3)) :
    guesses ≤ (q+H+E+2)^210 ∧ size ≤ (q+H+E+2)^210 := by
  let N := q+H+E+2
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hbase : E+H+W+2 ≤ N^2 := by dsimp [N]; ring_nf; omega
  have h100 := Nat.pow_le_pow_left hbase 100
  rw [← pow_mul] at h100
  have a : gates ≤ N^200 := hg.trans h100
  have b : guesses ≤ N^200 := hu.trans h100
  have c : N ≤ N^200 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0<N by omega) (show 1≤200 by decide)
  have lead : W+3*(E+H)+guesses ≤ 6*N^200 := by dsimp [N] at c ⊢; dsimp [N] at b; omega
  have mul : 2*q+1 ≤ 2*N := by dsimp [N]; omega
  have tail : 2*(2*W+3) ≤ 8*N := by dsimp [N]; omega
  have top : N^200 ≤ N^201 := Nat.pow_le_pow_right (by omega) (by decide)
  have absorb : 21 ≤ N^9 := (show 21 ≤ 2^9 by decide).trans (Nat.pow_le_pow_left hN 9)
  refine ⟨b.trans (Nat.pow_le_pow_right (by omega) (by decide : 200 ≤ 210)), ?_⟩
  change size ≤ N^210
  calc
    _ ≤ gates + (W+3*(E+H)+guesses)*(2*q+1) + 2*(2*W+3) := hs
    _ ≤ N^200 + (6*N^200)*(2*N) + 8*N := by gcongr
    _ ≤ 21*N^201 := by
      have hN' := c.trans top
      have prod : (6*N^200)*(2*N) = 12*N^201 := by
        rw [pow_succ N 200]
        change (6*N^200)*(2*N) = (6*2)*(N^200*N)
        exact mul_mul_mul_comm 6 (N^200) 2 N
      rw [prod]
      omega
    _ ≤ N^9 * N^201 := Nat.mul_le_mul_right _ absorb
    _ = N^210 := (pow_add N 9 201).symm

/-- At any of the `D ≤ m` crossing stages, `q + H + E + 2` is at most `(q+2)^2`.
Consequently a bound from the local checker applies with the same polynomial in `q`
to every stage, every orientation, and both sides. -/
theorem factorChecker_stage_budget {q H E D m s : ℕ}
    (hD : D ≤ m) (hm : m ≤ q) (hH : 2*H ≤ q) (hE : E ≤ D*H)
    (h : s ≤ (q+H+E+2)^210) : s ≤ (q+2)^420 := by
  have hE' : E ≤ q^2 := by
    rw [pow_two]
    exact hE.trans (Nat.mul_le_mul (hD.trans hm) (by omega))
  have hb : q+H+E+2 ≤ (q+2)^2 := by ring_nf; omega
  calc
    _ ≤ (q+H+E+2)^210 := h
    _ ≤ ((q+2)^2)^210 := Nat.pow_le_pow_left hb 210
    _ = (q+2)^(2*210) := (pow_mul (q+2) 2 210).symm
    _ = (q+2)^420 := congrArg (fun t : ℕ => (q+2)^t) (by decide : 2*210=420)

end Crossing

end BorderVNP
end Computability
end OAI
