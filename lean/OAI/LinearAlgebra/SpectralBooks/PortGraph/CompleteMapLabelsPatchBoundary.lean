import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsViews

/-! # Counting the distinct boundary wires from local numbered slots -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PortGraph.MapLabels

open PlanarPatch Finset
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (M : RootedMap V E)

private theorem local_card (R P : Finset V) (v : V) :
    (univ.filter (fun p : M.graph.Port v => otherEnd M.graph p ∈ R \ P)).card =
    (univ.filter (fun i : Fin 4 => ∃ w j, M.graph.portStep M.slots v i = some (w,j) ∧
      w ∈ R ∧ w ∉ P)).card := by
  apply card_nbij (M.slots v)
  · intro p hp
    exact mem_filter.mpr ⟨mem_univ _, _, _, M.graph.portStep_port M.slots p,
      mem_sdiff.mp (mem_filter.mp hp).2⟩
  · exact (M.slots v).injective.injOn
  · intro i hi
    obtain ⟨w,j,hs,hw⟩ := (mem_filter.mp hi).2
    by_cases h : ∃ p, M.slots v p = i
    · obtain ⟨p,rfl⟩ := h
      rw [portStep_port, Option.some.injEq, Prod.mk.injEq] at hs
      rw [← hs.1] at hw
      exact ⟨p, mem_filter.mpr ⟨mem_univ _, mem_sdiff.mpr hw⟩, rfl⟩
    · rw [portStep_missing _ _ _ _ h] at hs
      contradiction

/-- The boundary counts wire identifiers. Each boundary wire has exactly one numbered
slot in the patch leading to another vertex of the remaining set outside the patch. -/
theorem boundary_card_eq_slots (R P : Finset V) :
    (boundary M.graph.tail M.graph.head R P).card = ∑ v ∈ P,
      (univ.filter (fun i : Fin 4 => ∃ w j, M.graph.portStep M.slots v i = some (w,j) ∧
        w ∈ R ∧ w ∉ P)).card := by
  classical
  let f (d : E × Bool) : ℕ := if M.graph.vertex d.1 d.2 ∈ P ∧
    M.graph.vertex d.1 (!d.2) ∈ R \ P then 1 else 0
  let e := Equiv.sigmaFiberEquiv (fun d : E × Bool => M.graph.vertex d.1 d.2)
  calc
    _ = ∑ d : E × Bool, f d := by
      rw [boundary, card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
      apply sum_congr rfl
      intro d _
      rw [Fintype.sum_bool]
      by_cases ht : M.graph.tail d ∈ P <;> by_cases hh : M.graph.head d ∈ P <;>
        simp [f, vertex, ht, hh]
    _ = ∑ v, ∑ p : M.graph.Port v, f p.val := by
      rw [← e.sum_comp f]
      exact Fintype.sum_sigma _
    _ = ∑ v, if v ∈ P then (univ.filter (fun p : M.graph.Port v =>
        otherEnd M.graph p ∈ R \ P)).card else 0 := by
      apply sum_congr rfl
      intro v _
      have src (p : M.graph.Port v) : M.graph.vertex p.val.1 p.val.2 = v := p.property
      simp only [f, src, otherEnd]
      by_cases hv : v ∈ P <;> simp [hv]
    _ = _ := by
      rw [← sum_filter]
      simp only [filter_mem_eq_inter, univ_inter]
      exact sum_congr rfl (fun v _ => local_card M R P v)

end PortGraph.MapLabels

end SpectralBooks
end LinearAlgebra
end OAI
