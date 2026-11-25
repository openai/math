import OAI.Hierarchy.ProbeChainPlacement
import OAI.Hierarchy.ProbeNamedChainReads

namespace OAI
/-! # Reading physical strip coordinates at the rank ordering of their actual sites -/

namespace Hierarchy.ProbeStage
open AdaptiveProbe ChainStrip
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [Field F] {h d k : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : StageAt h d → (Fin k × Bool) → Finset (Fin (2^h)))

def namedStrip {J : ℕ} (global : ColumnSite (StageColumns h d) k ↪ Fin J) (path : LiveChains S π depth marked) :=
  SiteOrder.ofEmbedding ((stripSites S π depth marked path).trans global)

/-- This equality ties every ordinal in the histogram's order embedding to the exact
live record, stage/group/socket, or signed catalyst layer that owns that local site. -/
theorem sorted_physical_site {J : ℕ} (global : ColumnSite (StageColumns h d) k ↪ Fin J)
    (path : LiveChains S π depth marked) (i : Site depth k) : let physical := namedStrip S π depth marked global path
    physical.ord (physical.name i)=global (stripSites S π depth marked path i) := (namedStrip S π depth marked global path).reconstruct i

/-- The same discrepancy cutoff works on every installed strip, including whenever
two paths order their local sockets in different ways on the final Wnet board. -/
theorem all_named_frames (hk : 0<k) (no : ¬HasSpectralFlat F (k+1)) {η : ℝ} (tol : 0<η) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∃ ε : ℝ, 0<ε ∧ ∀ {J : ℕ} (global : ColumnSite (StageColumns h d) k ↪ Fin J)
    (path : LiveChains S π depth marked) (post : Commodity (Fin (2^h)) (permutationFabric h d).shapes.length k → ℝ),
    (∀ j, 0≤postQuote S π depth marked path post j ∧ postQuote S π depth marked path post j≤(M:ℝ)+1) →
    namedError F depth k (namedStrip S π depth marked global path).name M (postQuote S π depth marked path post) ≤ ε →
    Nonempty (ChainFrame S π depth marked path M η post) := by
  obtain ⟨N,each⟩ := sorted_reads (F:=F) depth k hk no tol
  refine ⟨N,?_⟩; intro M enough
  obtain ⟨ε,he,reads⟩ := each M enough
  refine ⟨ε,he,?_⟩; intro J global path post box pass
  obtain ⟨zi,zo,joined,all,last⟩ := reads _ _ ⟨fun i => (box i).1,fun i => (box i).2⟩ pass
  exact ⟨⟨zi,zo,joined,fun j => (all (j,path.2.1)).le,last.le⟩⟩

end
end Hierarchy.ProbeStage

end OAI
