import OAI.Computability.VPVNP.RAMSortReplay
import OAI.Computability.VPVNP.RAMSortCorrect
import OAI.Computability.VPVNP.RAMSortPerm
import OAI.LinearAlgebra.SpectralBooks.Batcher
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort

namespace OAI
/-! # The addressed RAM comparator schedule and the ascending sorter -/

namespace ThreeFlat.Routing.StableCompactStages

open Computability.VPVNP.RAMSort

variable {α : Type*} [LinearOrder α] {m : ℕ}

def steps (m : ℕ) := phases m m le_rfl

def run (ss : List (Stage m)) (x : ℕ → α) :=
  ss.foldl (fun y s => comparatorLayer s.stride (phaseDirection s.phase) y) x

private theorem run_strides (b a : ℕ) (ha : a ≤ b) (q : ℕ) (hq : q ≤ a) (x : ℕ → α) :
    run (strides b a ha q hq) x = runStrides q (phaseDirection a) x := by
  induction q generalizing x with
  | zero => rfl
  | succ q ih =>
    change run (strides b a ha q _) (comparatorLayer q (phaseDirection a) x) = _
    rw [ih,runStrides]

private theorem run_phases (b a : ℕ) (ha : a ≤ b) (x : ℕ → α) :
    run (phases b a ha) x = runPhases a x := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [phases,run,List.foldl_append]
    change run (strides b (a+1) _ _ _) (run (phases b a _) x) = _
    rw [ih,run_strides,runPhases]

/-- Both finite sorting networks return the same monotone permutation. -/
theorem sorted_block (m : ℕ) (x : ℕ → α) :
    block m 0 (run (steps m) x) = (LinearAlgebra.SpectralBooks.Batcher.sortNet m).eval (block m 0 x) := by
  rw [steps,run_phases,block_runPhases]
  let v := block m 0 x
  change sort m true v = (LinearAlgebra.SpectralBooks.Batcher.sortNet m).eval v
  obtain ⟨mono,π,eq⟩ := LinearAlgebra.SpectralBooks.Batcher.sortNet_correct v
  have perm : (List.ofFn ((LinearAlgebra.SpectralBooks.Batcher.sortNet m).eval v)).Perm (List.ofFn v) := by
    rw [eq]
    exact π.ofFn_comp_perm v
  apply List.ofFn_injective
  exact ((sort_perm m true v).trans perm.symm).eq_of_sortedLE
    (sort_monotone m v).sortedLE_ofFn mono.sortedLE_ofFn

end ThreeFlat.Routing.StableCompactStages

end OAI
