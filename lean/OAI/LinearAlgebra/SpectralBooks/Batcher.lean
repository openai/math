import OAI.LinearAlgebra.SpectralBooks.BitonicMerge
import OAI.LinearAlgebra.SpectralBooks.BitonicPermutation
import OAI.LinearAlgebra.SpectralBooks.ComparatorCuts

namespace OAI
/-! # Correctness and cost of Batcher sorting for batched coefficient queries

On blocks of `2^k` records the fixed schedule yields an ascending permutation of
the inputs in `k(k+1)/2` comparator layers and `2^k k(k+1)/4` compare-exchanges.
-/

namespace LinearAlgebra.SpectralBooks.Batcher

/-- The zero-one principle for any concrete schedule, including arbitrary fixed rewirings. -/
theorem Network.monotone_of_bit_inputs {k : ℕ} {α : Type*} [LinearOrder α] (N : Network k)
    (h : ∀ b : Wires k Bool, Monotone (N.eval b)) (x : Wires k α) : Monotone (N.eval x) :=
  monotone_of_zeroOne N.eval N.eval (fun t a ↦ N.eval_comp _ (monotone_thresholdCut t) a) h x

/-- Batcher's recursively constructed sorting network sorts arbitrary linearly ordered records. -/
theorem sortNet_monotone {k : ℕ} {α : Type*} [LinearOrder α] (x : Wires k α) :
    Monotone ((sortNet k).eval x) := by
  induction k with
  | zero =>
    intro i j _
    have h : i = j := by
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      simp only [pow_zero] at hi hj
      omega
    exact le_of_eq (congrArg _ h)
  | succ k ih =>
    rw [sortNet_succ_eval]
    exact mergeNet_monotone _ _ (ih _) (ih _)

/-- Sorting preserves every record and its multiplicity, even in the presence of ties. -/
theorem sortNet_correct {k : ℕ} {α : Type*} [LinearOrder α] (x : Wires k α) :
    Monotone ((sortNet k).eval x) ∧
      ∃ e : Equiv.Perm (Fin (2^k)), (sortNet k).eval x = x ∘ e :=
  ⟨sortNet_monotone x, (sortNet k).exists_eval_eq_comp_perm x⟩

end LinearAlgebra.SpectralBooks.Batcher

end OAI
