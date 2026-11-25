import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPortRotation
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchCertificates
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchLocality

/-! # Canonical small-boundary patch partitions of spherical port graphs -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

universe u v

/-- There is a uniform size bound for a nonempty connected candidate in every
nonempty induced subgraph of a spherical port graph of maximum degree four. -/
theorem uniform_spherical_candidates (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ (V : Type u) (E : Type v) [DecidableEq V] [DecidableEq E] [Fintype E]
      (G : PortGraph V E) (ρ : G.Rotation), (underlying G.tail G.head).Connected →
      ρ.picture.GenusZero → (∀ v, Fintype.card (G.Port v) ≤ 4) →
      ∀ R : Finset V, R.Nonempty → ∃ P, Candidate G.tail G.head K ε R P := by
  have hδ : 0 < ε / (4 + ε) := by positivity
  obtain ⟨K, split⟩ := exists_smallPieces_of_balancedSeparators.{u} 11 _ (by norm_num) hδ
  refine ⟨K, ?_⟩
  intro V E _ _ _ G ρ hc hg hdeg R hR
  obtain ⟨D, hDR, blocks, hb, hsize, hcost⟩ := split V _ R (ρ.balancedSeparators hc hg R)
  have hcover : blocks.biUnion id = R \ D := by
    ext x
    exact Finset.mem_biUnion.trans ⟨fun ⟨P, hP, hx⟩ => hb.subset P hP hx, hb.cover x⟩
  obtain ⟨hsurv, hbudget⟩ := budget_of_deletion_fraction hR hDR hε.le hcost
  obtain ⟨P, _, hP⟩ := exists_candidate_of_deletions G.tail G.head R D blocks K ε hsurv
    hcover hb.disjoint (fun P hP => edgeClosed_of_adj _ _ _ _ (hb.closed P hP))
    (fun P hP => ⟨Finset.nonempty_coe_sort.mp (hb.connected P hP).nonempty, hb.connected P hP, hsize P hP⟩)
    (fun v _ => (card_incidentEdges_le_ports G v).trans (hdeg v)) hbudget
  exact ⟨P, hP⟩

/-- The canonical patch families on a spherical map partition its vertices,
cut at most `ε |V|` edge identifiers, and have uniquely accepted removal
records. The cutoff is fixed before the map or its vertex bound is given. -/
theorem uniform_spherical_patch_partition (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ (V : Type u) (E : Type v) [Fintype V] [DecidableEq V] [DecidableEq E] [Fintype E]
      (G : PortGraph V E) (ρ : G.Rotation), (underlying G.tail G.head).Connected →
      ρ.picture.GenusZero → (∀ v, Fintype.card (G.Port v) ≤ 4) →
      ∀ (key : V ↪ ℕ) (N : ℕ), Fintype.card V ≤ N →
        let vertices : Finset V := Finset.univ
        let blocks := canonicalBlocks key G.tail G.head K ε vertices N
        blocks.biUnion id = vertices ∧ (↑blocks : Set (Finset V)).PairwiseDisjoint id ∧
        (∀ P ∈ blocks, P.Nonempty ∧ Connected G.tail G.head P ∧ P.card ≤ K) ∧
        ((crossing G.tail G.head vertices blocks).card : ℝ) ≤ ε * Fintype.card V ∧
        ∃! record : V → ℕ × ℕ, RecordsValid key (candidatesOn G.tail G.head K ε) vertices N record := by
  obtain ⟨K, hk⟩ := uniform_spherical_candidates.{u,v} ε hε
  refine ⟨K, ?_⟩
  intro V E _ _ _ _ G ρ hc hg hdeg key N hN
  let C := candidatesOn G.tail G.head K ε
  have hex := hk V E G ρ hc hg hdeg
  have hsound : ∀ ⦃R P⦄, P ∈ C R → P.Nonempty ∧ P ⊆ R :=
    fun _ _ h => ⟨(mem_candidatesOn.mp h).1, (mem_candidatesOn.mp h).2.1⟩
  have hnon : ∀ ⦃R⦄, R.Nonempty → (C R).Nonempty := by
    intro R hR
    obtain ⟨P, hp⟩ := hex R hR
    exact ⟨P, mem_candidatesOn.mpr hp⟩
  have hn : (Finset.univ : Finset V).card ≤ N := by simpa using hN
  obtain ⟨cover, disj, sizes, bound⟩ :=
    (canonical_peeling key G.tail G.head K ε Finset.univ (fun R _ => hex R) hn).partition
  obtain ⟨record, hrecord⟩ := exists_recordsValid key C hsound hnon hn
  refine ⟨cover, disj, sizes, by simpa using bound, record, hrecord, ?_⟩
  intro other hother
  exact funext fun v => recordsValid_unique key C hsound hnon hother hrecord v (Finset.mem_univ _)

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
