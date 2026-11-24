import OAI.Computability.VPVNP.CycleCriterion
import OAI.Computability.VPVNP.CycleQueryRow

/-!
# Exact query budget for the Hamiltonian matrix check

Starting from the distinguished root, the finite-control program scans one row
per vertex in the putative cycle. A successful traversal uses exactly one read
per column of each of its `m` rows.
-/

namespace OAI
namespace Computability
namespace VPVNP

variable {m : ℕ} (root : Fin m) (x : Fin m × Fin m → Bool)

/-- The row and first-return checks that are still pending at the start of row `t`. -/
private def passesFrom (t : ℕ) : Prop :=
  (∀ k : ℕ, t ≤ k → k < m → RowValid x ((rowSuccessor x)^[k] root)) ∧
  (∀ k : ℕ, t < k → k < m → (rowSuccessor x)^[k] root ≠ root) ∧
  (rowSuccessor x)^[m] root = root

private theorem passesFrom_succ {t : ℕ} (ht : t + 1 < m) :
    passesFrom root x t ↔ RowValid x ((rowSuccessor x)^[t] root) ∧
      (rowSuccessor x)^[t + 1] root ≠ root ∧ passesFrom root x (t + 1) := by
  constructor
  · rintro ⟨rows, before, finish⟩
    exact ⟨rows t le_rfl (by omega), before _ (by omega) ht,
      fun k hk hkm => rows k (by omega) hkm, fun k hk hkm => before k (by omega) hkm, finish⟩
  · rintro ⟨row, next, rows, before, finish⟩
    refine ⟨fun k hk hkm => ?_, fun k hk hkm => ?_, finish⟩
    · by_cases h : k = t
      · simpa [h] using row
      · exact rows k (by omega) hkm
    · by_cases h : k = t + 1
      · simpa [h] using next
      · exact before k (by omega) hkm

private theorem passesFrom_last {t : ℕ} (ht : t + 1 = m) :
    passesFrom root x t ↔ RowValid x ((rowSuccessor x)^[t] root) ∧
      (rowSuccessor x)^[t + 1] root = root := by
  constructor
  · rintro ⟨rows, _, finish⟩
    exact ⟨rows _ le_rfl (by omega), ht.symm ▸ finish⟩
  · rintro ⟨row, finish⟩
    refine ⟨fun k hk hkm => ?_, fun k hk hkm => ?_, ht ▸ finish⟩
    · have h : k = t := by omega
      simpa [h] using row
    · omega

private theorem cycleQuery_eval_from (t : Fin m) :
    (cycleQuery root).eval (x ∘ finProdFinEquiv.symm) ((m - t.val) * m)
      (.inr (t, (rowSuccessor x)^[t.val] root, ⟨0, root.pos⟩, none)) = true ↔
      passesFrom root x t.val := by
  have ht := t.isLt
  have hfuel : (m - t.val) * m = (m - (t.val + 1)) * m + m := by
    rw [← Nat.succ_mul, show (m - (t.val + 1)).succ = m - t.val by omega]
  rw [hfuel, cycleQuery_eval_row]
  have hvisit : rowSuccessor x ((rowSuccessor x)^[t.val] root) =
      (rowSuccessor x)^[t.val + 1] root := (Function.iterate_succ_apply' ..).symm
  by_cases row : RowValid x ((rowSuccessor x)^[t.val] root)
  · have rowBits := row
    unfold RowValid at rowBits
    rw [ite_eq_left rowBits, hvisit]
    by_cases h : t.val + 1 < m
    · rw [passesFrom_succ root x h, and_iff_right row]
      simp only [afterRow, dite_eq_left h]
      by_cases early : (rowSuccessor x)^[t.val + 1] root = root
      · simp [early]
      · rw [ite_eq_right early, and_iff_right early]
        exact cycleQuery_eval_from ⟨_, h⟩
    · rw [passesFrom_last root x (by omega), and_iff_right row]
      simp only [afterRow, dite_eq_right h, cycleQuery_eval_halt, beq_iff_eq]
  · have rowBits := row
    unfold RowValid at rowBits
    rw [ite_eq_right rowBits]
    exact ⟨fun h => by contradiction, fun hp => (row (hp.1 _ le_rfl t.isLt)).elim⟩
termination_by m - t.val
decreasing_by omega


/-- The matrix query program decides the directed spanning-cycle predicate with
a budget of exactly `m * m` payload queries. -/
theorem cycleQuery_eval_iff (root : Fin m) (x : Fin m × Fin m → Bool) :
    (cycleQuery root).eval (x ∘ finProdFinEquiv.symm) (m * m) (cycleQuery root).start = true ↔
      x ∈ (spanningCycles m).image permutationEdges := by
  rw [mem_spanningCycleEdges_iff_firstReturn]
  have start := cycleQuery_eval_from root x ⟨0, root.pos⟩
  simp only [Nat.sub_zero, Function.iterate_zero, id_eq] at start
  rw [show (cycleQuery root).start = .inr (⟨0, root.pos⟩, root, ⟨0, root.pos⟩, none) by rfl, start]
  unfold passesFrom
  refine and_congr_left fun _ => ⟨fun rows k => rows k.val (Nat.zero_le _) k.isLt, ?_⟩
  exact fun rows k _ hk => rows ⟨k, hk⟩

end VPVNP
end Computability
end OAI
