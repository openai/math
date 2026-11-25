import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace OAI
/-! # Pool size for narrow recursive calls

Each call has capacity `H`, with one thousandth of its positions available for
routing slack. Classes fill separate batches. The estimates include one terminal
batch per class and rounding the common pool down to an integer.
-/

namespace ThreeFlat.Routing

open scoped BigOperators

/-- Number of batches for one class of units with active capacity `capacity`. -/
def poolBatchCount (count capacity : ℕ) : ℕ := (count + capacity - 1) / capacity

/-- A pool occupying at most 1.29 times the parent payload has a spare
thousandth of its calls, after accommodating 1.25 times the payload and
charging one last batch per class at one percent of the parent payload. -/
theorem callPoolBudget {I : Type*} [Fintype I] (c : I → ℕ) (H U W : ℕ)
    (size : 1000 ≤ H) (width : 0 < U)
    (occupied : 100 * (∑ i, c i) * U ≤ 125 * W)
    (last : 100 * Fintype.card I * (H*U) ≤ W) :
    let capacity := 999*H/1000
    let K := 129*W/(100*(H*U))
    1000*(∑ i, poolBatchCount (c i) capacity) + K ≤ 1000*K := by
  classical
  let t := 999*H/1000
  let D := H*U
  let K := 129*W/(100*D)
  let B := ∑ i, poolBatchCount (c i) t
  change 1000*B + K ≤ 1000*K
  by_cases empty : IsEmpty I
  · let _ := empty
    simp [B]
    omega
  let _ : Nonempty I := not_isEmpty_iff.mp empty
  have hcard : 1 ≤ Fintype.card I := Fintype.card_pos
  have hd : 0 < D := Nat.mul_pos (by omega) width
  have hround : 998*H ≤ 1000*t := by dsimp [t]; omega
  have ht : t ≤ H := by dsimp [t]; omega
  have classD : 100*D ≤ W := by
    have h := Nat.mul_le_mul_right (100*D) hcard
    dsimp only [D] at *
    nlinarith only [h,last]
  have batch : B*t ≤ (∑ i, c i) + Fintype.card I*t := by
    unfold B
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ i, (c i + t) := Finset.sum_le_sum fun i _ =>
        (Nat.div_mul_le_self (c i+t-1) t).trans (Nat.sub_le ..)
      _ = _ := by simp [Finset.sum_add_distrib]
  have scaled : 998*(B*D) ≤ 1260*W := by
    have h1 := Nat.mul_le_mul_right (B*U) hround
    have h2 := Nat.mul_le_mul_right (1000*U) batch
    have h3 := Nat.mul_le_mul_right (1000*Fintype.card I*U) ht
    dsimp only [D]
    nlinarith only [h1,h2,h3,occupied,last]
  have kround : 129*W < (K+1)*(100*D) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 100*D)).mp
    exact Nat.lt_succ_self K
  have floor : 128*W ≤ 100*(K*D) := by nlinarith only [kround,classD]
  have hh : (1000*B+K)*D ≤ (1000*K)*D := by
    nlinarith only [scaled,floor]
  exact Nat.le_of_mul_le_mul_right hh hd

end ThreeFlat.Routing

end OAI
