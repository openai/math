import OAI.ThreeFlat.Concentrator.Greedy
import Mathlib.Data.Finset.Sort

namespace OAI
namespace ThreeFlat.Concentrator.Greedy

variable {R : Type*} [LinearOrder R]

/-- A prefix of a sorted processing order contains exactly its earlier active slots. -/
theorem mem_sort_prefix_iff {A : Finset R} {prior later : List R} {i q : R}
    (order : A.sort = prior ++ i :: later) : q ∈ prior ↔ q ∈ A ∧ q < i := by
  have sorted := A.sortedLT_sort.pairwise
  rw [order, List.pairwise_append] at sorted
  have mem : q ∈ A ↔ q ∈ prior ∨ q = i ∨ q ∈ later := by
    rw [← Finset.mem_sort (· ≤ ·), order, List.mem_append, List.mem_cons]
  constructor
  · intro hp
    exact ⟨mem.mpr (Or.inl hp), sorted.2.2 q hp i List.mem_cons_self⟩
  · rintro ⟨ha, hlt⟩
    rcases mem.mp ha with hp | rfl | hq
    · exact hp
    · exact (lt_irrefl _ hlt).elim
    · exact (hlt.asymm ((List.pairwise_cons.mp sorted.2.1).1 q hq)).elim

/-- On a sorted neighborhood, the first free port is its least free element. -/
theorem firstFree_sort_eq_some {S F : Finset R} (r : R) (hr : r ∈ S) (hf : r ∈ F)
    (least : ∀ q ∈ S, q ∈ F → r ≤ q) : firstFree S.sort F = some r := by
  obtain ⟨prior,later,order⟩ := List.append_of_mem ((Finset.mem_sort (· ≤ ·)).mpr hr)
  refine List.find?_eq_some_iff_append.mpr ⟨by simpa using hf, prior,later,order,?_⟩
  intro q hq
  have ⟨ha,hlt⟩ := (mem_sort_prefix_iff order).mp hq
  simpa using (fun hqF : q ∈ F => hlt.not_ge (least q ha hqF))

end ThreeFlat.Concentrator.Greedy

end OAI
