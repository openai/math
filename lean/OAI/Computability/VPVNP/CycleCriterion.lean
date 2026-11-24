import OAI.Computability.VPVNP.Hamiltonian
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Recognizing a spanning cycle by its first return

A walk from one root can check a Boolean adjacency matrix one row at a time.
If it first returns to the root after exactly as many steps as there are vertices,
the visited rows comprise the whole matrix.
-/

namespace OAI
namespace Computability
namespace VPVNP

open Function

/-- The scanned successor is the only true entry of the row. -/
def RowValid {m : ℕ} (x : Fin m × Fin m → Bool) (i : Fin m) : Prop :=
  ∀ j, x (i, j) = decide (rowSuccessor x i = j)

/-- A row-by-row walk accepts exactly the adjacency matrices of spanning cycles.
It rejects a missing or ambiguous outgoing edge on any visited row, as well as
a return to the root before the final step. -/
theorem mem_spanningCycleEdges_iff_firstReturn {m : ℕ} (root : Fin m)
    (x : Fin m × Fin m → Bool) :
    x ∈ (spanningCycles m).image permutationEdges ↔
      (∀ k : Fin m, RowValid x ((rowSuccessor x)^[k.val] root)) ∧
      (∀ k : ℕ, 0 < k → k < m → (rowSuccessor x)^[k] root ≠ root) ∧
      (rowSuccessor x)^[m] root = root := by
  classical
  have hm := Nat.zero_lt_of_lt root.isLt
  constructor
  · intro hx
    obtain ⟨π, hπ, rfl⟩ := Finset.mem_image.mp hx
    have hcyc : π.IsCycleOn (Finset.univ : Finset (Fin m)) := by
      simpa [spanningCycles, hm] using hπ
    simp only [RowValid, rowSuccessor_permutationEdges]
    refine ⟨fun _ _ => rfl, ?_, ?_⟩
    · intro k hk hkm heq
      have hdvd : m ∣ k := by
        simpa using (hcyc.pow_apply_eq (Finset.mem_univ root)).1 heq
      exact hkm.not_ge (Nat.le_of_dvd hk hdvd)
    · simpa [Equiv.Perm.coe_pow] using hcyc.pow_card_apply (Finset.mem_univ root)
  · rintro ⟨hrow, hfirst, hreturn⟩
    let f := rowSuccessor x
    have hp : IsPeriodicPt f m root := hreturn
    have hmin : minimalPeriod f root = m := by
      apply (hp.minimalPeriod_le hm).antisymm
      exact le_of_not_gt fun h =>
        hfirst _ (hp.minimalPeriod_pos hm) h (iterate_minimalPeriod (f := f) (x := root))
    let visit (k : Fin m) := f^[k.val] root
    have hinj : Injective visit := by
      intro i j h
      apply Fin.ext
      exact (iterate_eq_iterate_iff_of_lt_minimalPeriod
        (hmin.symm ▸ i.isLt) (hmin.symm ▸ j.isLt)).mp h
    have hreach : Surjective visit := Finite.injective_iff_surjective.mp hinj
    apply (acceptsCycleMatrix_iff root x).mp
    rw [acceptsCycleMatrix, decide_eq_true_eq]
    refine ⟨?_, ?_, hreach⟩
    · intro i
      obtain ⟨k, rfl⟩ := hreach i
      exact hrow k
    · intro j
      obtain ⟨k, rfl⟩ := hreach j
      exact periodicPts_subset_range (mk_mem_periodicPts hm (hp.apply_iterate k.val))

end VPVNP
end Computability
end OAI
