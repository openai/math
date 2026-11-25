import OAI.LinearAlgebra.SpectralBooks.BitonicNetwork
import OAI.LinearAlgebra.SpectralBooks.BitonicRuns

namespace OAI
/-! # Correctness of the bitonic merge

At any threshold the lower cut of a bitonic input is an interval of the
cyclically ordered wires. The two outputs of the first comparator layer have
circular cuts of lengths `min m n` and `m - n` when the input has `2*n` wires
and its cut has length `m`. Recursive merging makes both cuts initial segments.
-/

namespace LinearAlgebra.SpectralBooks.Batcher

private def halfStart (n s : ℕ) : ℕ := if s < n then s else s - n

private theorem halfStart_lt {n s : ℕ} (hs : s < n + n) : halfStart n s < n := by
  unfold halfStart
  split <;> omega

private theorem cyclicCut_halves_or {n s m i : ℕ} (hs : s < n+n) (hm : m ≤ n+n)
    (hi : i < n) :
    cyclicCut (n+n) s m i ∨ cyclicCut (n+n) s m (n+i) ↔
      cyclicCut n (halfStart n s) (min m n) i := by
  by_cases h : s < n <;> by_cases h' : m ≤ n <;>
    simp only [cyclicCut, halfStart, h, ite_true, ite_false, min_def, h'] <;> omega

private theorem cyclicCut_halves_and {n s m i : ℕ} (hs : s < n+n) (hm : m ≤ n+n)
    (hi : i < n) :
    cyclicCut (n+n) s m i ∧ cyclicCut (n+n) s m (n+i) ↔
      cyclicCut n (halfStart n s) (m - n) i := by
  by_cases h : s < n <;>
    simp only [cyclicCut, halfStart, h, ite_true, ite_false] <;> omega

/-- Half-cleaners compress a circular cut to the initial segment of the same
length. This describes the output at every threshold, including ties. -/
theorem mergeNet_lower_cut {α : Type*} [LinearOrder α] (k : ℕ) (c : α) :
    ∀ (x : Wires k α) {s m : ℕ}, s < 2^k → m ≤ 2^k →
      (∀ i, x i ≤ c ↔ cyclicCut (2^k) s m i.val) →
      ∀ i, (mergeNet k).eval x i ≤ c ↔ i.val < m := by
  induction k with
  | zero =>
    intro x s m hs hm hx i
    simp only [mergeNet, Network.eval, hx i, cyclicCut, pow_zero]
    have hi := i.isLt
    simp only [pow_zero] at hi hs hm
    omega
  | succ k ih =>
    intro x s m hs hm hx i
    have hsize : 2^(k+1) = 2^k + 2^k := by rw [pow_succ, Nat.mul_two]
    rw [hsize] at hs hm
    have hstart := halfStart_lt hs
    rw [mergeNet_succ_eval]
    rcases low_or_high i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [join_low, low_val, ih _ hstart (min_le_right m (2^k))]
      · exact (lt_min_iff.trans ⟨And.left, fun h => ⟨h, j.isLt⟩⟩)
      · intro t
        simp only [min_le_iff, hx, low_val, high_val, hsize]
        exact cyclicCut_halves_or hs hm t.isLt
    · rw [join_high, high_val, ih _ hstart (show m - 2^k ≤ 2^k by omega)]
      · omega
      · intro t
        simp only [max_le_iff, hx, low_val, high_val, hsize]
        exact cyclicCut_halves_and hs hm t.isLt

/-- The ascending bitonic merge sorts an ascending run followed by a descending
run of the same length. -/
theorem mergeNet_monotone {α : Type*} [LinearOrder α] {k : ℕ} (a b : Wires k α)
    (ha : Monotone a) (hb : Monotone b) :
    Monotone ((mergeNet (k+1)).eval (join a (fun i => b (Fin.rev i)))) := by
  let x := join a (fun i => b (Fin.rev i))
  intro i j hij
  let c := (mergeNet (k+1)).eval x j
  obtain ⟨s, hs, m, hm, ha', hb'⟩ := sorted_pair_cyclicCut (by positivity) ha hb c
  have hsize : 2^(k+1) = 2^k + 2^k := by rw [pow_succ, Nat.mul_two]
  rw [← hsize] at hs hm ha' hb'
  have hx (t : Fin (2^(k+1))) : x t ≤ c ↔ cyclicCut (2^(k+1)) s m t.val := by
    rcases low_or_high t with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · simpa only [x, join_low, low_val] using ha' u
    · simpa only [x, join_high, high_val] using hb' u
  have hcut := mergeNet_lower_cut (k+1) c x hs hm hx
  exact (hcut i).mpr (lt_of_le_of_lt hij ((hcut j).mp (le_refl c)))

end LinearAlgebra.SpectralBooks.Batcher

end OAI
