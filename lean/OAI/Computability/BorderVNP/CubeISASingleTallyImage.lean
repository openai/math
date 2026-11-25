import OAI.Computability.BorderVNP.CubeISASingleTallyFamily
import OAI.Computability.BorderVNP.CubeISARowAccumSubtotals

/-! # Exact memory image of a row's accepted singleton intervals

The prefix sum ranges over the numeric trials of one ordered row. A failed
trial contributes zero; an accepted pair contributes all scalar offsets in
its padded interval. These are exactly the physical singleton slots.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SingleTally

open Cube Cube.Physical Cube.RowAccum Cube.Physical.Owned Finset

variable {n d : ℕ} (i : Fin (n+1)) (a b : Fin d)

/-- The two full packed labels decoded at this ordered row trial. -/
def labels (t : Fin (singlePairTrials n d)) : ℕ × ℕ :=
  let u := (singleOrderedPairs i a b t).val
  ((finFunctionFinEquiv u.1).val, (finFunctionFinEquiv u.2).val)

/-- Contribution of one accepted trial to an individual addressed memory word. -/
def contribution (base bits : ℕ) (t : Fin (singlePairTrials n d)) (addr : ℕ) : ℕ :=
  if singleTrialValid i a b t then
    familyImage (fun _ => 0) base (n+1) d (labels i a b t).1 (labels i a b t).2 bits addr
  else 0

/-- Memory after processing the first `k` numeric trials. -/
def prefixImage (base bits : ℕ) (before : ℕ → ℕ) (k x : ℕ) : ℕ :=
  before x + ∑ t ∈ range k, if ht : t < singlePairTrials n d then
    contribution i a b base bits ⟨t,ht⟩ x else 0

/-- Every earlier memory subtotal is bounded by every later one. -/
theorem prefix_le (base bits : ℕ) (before : ℕ → ℕ) {k l : ℕ} (h : k ≤ l) (x : ℕ) :
    prefixImage i a b base bits before k x ≤ prefixImage i a b base bits before l x :=
  Nat.add_le_add_left (Finset.sum_le_sum_of_subset (Finset.range_mono h)) _

/-- A valid trial applies exactly the aggregate native family update. -/
theorem prefix_visit (base bits : ℕ) (before : ℕ → ℕ) (t : Fin (singlePairTrials n d))
    (hv : singleTrialValid i a b t) :
    prefixImage i a b base bits before (t.val+1) =
      familyImage (prefixImage i a b base bits before t.val) base (n+1) d (labels i a b t).1
        (labels i a b t).2 bits := by
  funext x
  simp [prefixImage, sum_range_succ, t.isLt, contribution, hv, familyImage, Nat.add_assoc]

/-- Failed label pairs consume no scalar-interval work and make no memory change. -/
theorem prefix_skip (base bits : ℕ) (before : ℕ → ℕ) (t : Fin (singlePairTrials n d))
    (hv : ¬singleTrialValid i a b t) :
    prefixImage i a b base bits before (t.val+1) = prefixImage i a b base bits before t.val := by
  funext x
  simp [prefixImage, sum_range_succ, t.isLt, contribution, hv]

/-- At a row word, the last prefix is the starting word plus the sum of
the actual physical crossing counts in this orientation. -/
theorem final_cut {blocks h K : ℕ} (base B s : ℕ) (before : ℕ → ℕ)
    (select : Packet n d blocks → Selector n K h) (j : Fin (n+1)) :
    prefixImage i a b base (blocks*(h*B)) before (singlePairTrials n d) (base+j) =
      before (base+j) + ∑ k : SingleScan blocks (h*B) i a b,
        crossCount B s select (.inr (singleOrderedEquiv blocks (h*B) i a b k).val) j := by
  classical
  rw [prefixImage, ← Fin.sum_univ_eq_sum_range, Fintype.sum_prod_type]
  congr 1
  simp only [Fin.is_lt, dite_true, Fin.eta, contribution, ← Finset.sum_filter]
  rw [Finset.sum_subtype (p := singleTrialValid i a b) (Finset.univ.filter (singleTrialValid i a b)) (fun _ => by simp)]
  apply Finset.sum_congr rfl
  intro t _
  simp only [familyImage, zero_add, Nat.le_add_right, Nat.add_lt_add_iff_left,j.isLt,and_self,
    ite_true, Nat.add_sub_cancel_left]
  let f := fun k : Fin (blocks*(h*B)) => crossCount B s select (.inr (singleOrderedEquiv blocks (h*B)
    i a b (t,k)).val) j
  have he (k : Fin (blocks*(h*B))) : f k = unequalDigit d (labels i a b t.val).1 (labels i a b t.val).2 j :=
    (unequalDigit_crossCount B s select (singleOrderedEquiv blocks (h*B) i a b (t,k)).val j).symm
  change _ = ∑ k, f k
  simp [he]

/-- Memory words outside the declared row are invariant under the whole ordered pass. -/
theorem final_outside (base bits : ℕ) (before : ℕ → ℕ) (k x : ℕ) (hx : x < base ∨ base+(n+1) ≤ x) :
    prefixImage i a b base bits before k x = before x := by
  apply Nat.add_eq_left.mpr
  apply sum_eq_zero
  intro t _
  split
  · simp [contribution, familyImage, show ¬(base ≤ x ∧ x < base+(n+1)) by omega]
  · rfl

end RoutingISA.SingleTally

end BorderVNP
end Computability
end OAI
