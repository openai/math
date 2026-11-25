import OAI.Combinatorics.Sunflower.Placement.RuleSites
import OAI.Combinatorics.Sunflower.Placement
import OAI.Combinatorics.Sunflower.PlanarInput

/-! The finite planar placement realizes the geometric condition for every anchor rule
and has a positive global comparison deficit, all in one complex spectral point. -/

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Placement

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

variable {n : ℕ}

private theorem endsA_subset_fiber (n : ℕ) : endsA n ⊆ fiber 0 := by
  simp [endsA, Finset.insert_subset_iff]

private theorem endsB_subset_fiber (n : ℕ) : endsB n ⊆ fiber 1 := by
  simp [endsB, Finset.insert_subset_iff]

theorem exists_rule_sites (q : Rule (Fin (n + 2))) (hq : q ∈ anchorRules 0 1) :
    ∃ d : RuleSites q, d.Works width := by
  apply anchorRules_fin_cases (P := fun q => ∃ d : RuleSites q, d.Works width) _ _ _ _ hq
  · intro i
    refine ⟨⟨{a (interior i)}, {b (interior i)}, {z i}, by simp, by simp, by simp,
        by simp, by simp, by simp⟩, Or.inr ⟨z i, rfl, ?_⟩⟩
    change width (insert (z i) ({a (interior i)} ∪ {b (interior i)})) =
      width ({a (interior i)} ∪ {b (interior i)})
    rw [Finset.singleton_union]
    simpa only [bracket, Finset.union_singleton] using bracket_copy i
  · intro i
    refine ⟨⟨endsA n, {z i}, endsB n, by simp [endsA], by simp, by simp [endsB],
        endsA_subset_fiber n, by simp, endsB_subset_fiber n⟩, Or.inl ?_⟩
    simpa [triA, Finset.union_singleton] using gap_left i
  · intro i
    refine ⟨⟨endsB n, {z i}, endsA n, by simp [endsB], by simp, by simp [endsA],
        endsB_subset_fiber n, by simp, endsA_subset_fiber n⟩, Or.inl ?_⟩
    simpa [triB, Finset.union_singleton] using gap_right i
  · intro i j hij
    refine ⟨⟨{z i}, {z j}, matchPair i j, by simp, by simp, by simp [matchPair],
        by simp, by simp, by simp [matchPair, Finset.insert_subset_iff]⟩, Or.inl ?_⟩
    simpa [satPair] using gap_satellites hij

/-- A fixed complex point and placement for the `n+2` groups, chosen before the
alphabet or word length. -/
theorem exists_priced_placement (n : ℕ) :
    ∃ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Site n) ℂ → _ → Prop),
      0 < 1 - ∑ g : Fin (n + 2), maskDiagonalPrice φ 1 (fiber g) ∧
      ∀ q ∈ anchorRules (0 : Fin (n + 2)) 1,
        ∃ d : RuleSites q, d.Works (maskDiagonalPrice φ 1) := by
  classical
  obtain ⟨φ, hD, hφ⟩ := exists_planar_point (embedding n)
  let D := width (Finset.univ : Finset (Site n))
  have hD' : 0 < D := by simpa [D, width_eq _ Finset.univ_nonempty] using hD
  have price (s : Finset (Site n)) (hs : s.Nonempty) :
      maskDiagonalPrice φ 1 s = width s / D := by
    simpa [maskDiagonalPrice, rawLogPrice, D, width_eq s hs,
      width_eq _ Finset.univ_nonempty] using hφ s hs
  refine ⟨φ, ?_, ?_⟩
  · simp_rw [fun g => price (fiber g) (fiber_nonempty g)]
    rw [← Finset.sum_div, sub_pos, div_lt_one hD']
    exact sub_pos.mp (deficit_pos n)
  · intro q hq
    obtain ⟨d, hd⟩ := exists_rule_sites q hq
    exact ⟨d, d.works_normalize hD' price hd⟩

end Placement
end Sunflower
end Combinatorics
end OAI
