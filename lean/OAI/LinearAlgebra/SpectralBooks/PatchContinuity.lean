import OAI.LinearAlgebra.SpectralBooks.SpineConditioning
import OAI.LinearAlgebra.SpectralBooks.PatchIncrement
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Monoid

/-! # Continuity of the price of moving sites

An extra site can inherit a binary common label from any occupied site for the
cost of a single wire. Summing these relocation costs gives continuity even
when sites collide or approach the boundary of a convex patch.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set
open scoped Classical Topology
section

variable {E ι : Type*} [PseudoMetricSpace E] {C : Set E}

private theorem patchPrice_sub_le (δ : Finset E → ℝ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsub : IntersectingSubmodular δ)
    (hpair : ∀ x ∈ C, ∀ y ∈ C, δ {x, y} = dist x y)
    (S : Finset ι) (hS : S.Nonempty) (x y : ι → E)
    (hx : ∀ i ∈ S, x i ∈ C) (hy : ∀ i ∈ S, y i ∈ C) :
    δ (S.image y) - δ (S.image x) ≤ ∑ i ∈ S, dist (x i) (y i) := by
  let B := S.image x
  have he : S.image y ⊆ B ∪ S.image y := Finset.subset_union_right
  have hupper := (hmono (hS.image _) he).trans
    (conditioning_union_image_le_of_nonempty hmono hsub (hS.image x) S y)
  refine (sub_le_iff_le_add'.mpr hupper).trans (Finset.sum_le_sum fun i hi => ?_)
  have hxi : {x i} ⊆ B := Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem _ hi)
  have hsingle : δ {x i} = 0 := by simpa using hpair _ (hx i hi) _ (hx i hi)
  have h := price_increment_le_of_subset δ hmono hsub (Finset.singleton_nonempty _) hxi (y i)
  simpa only [hpair _ (hy i hi) _ (hx i hi), hsingle, sub_zero, dist_comm (y i)] using h

/-- Transport bound for a list of sites moving within the patch, with repetitions allowed. -/
theorem patchPrice_dist_le (δ : Finset E → ℝ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsub : IntersectingSubmodular δ)
    (hpair : ∀ x ∈ C, ∀ y ∈ C, δ {x, y} = dist x y)
    (S : Finset ι) (hS : S.Nonempty) (x y : ι → E)
    (hx : ∀ i ∈ S, x i ∈ C) (hy : ∀ i ∈ S, y i ∈ C) :
    dist (δ (S.image x)) (δ (S.image y)) ≤ ∑ i ∈ S, dist (x i) (y i) := by
  rw [Real.dist_eq, abs_le]
  constructor
  · linarith [patchPrice_sub_le δ hmono hsub hpair S hS x y hx hy]
  · simpa only [dist_comm] using patchPrice_sub_le δ hmono hsub hpair S hS y x hy hx

/-- A finite configuration moving continuously in a patch has a continuous diagonal price. -/
theorem continuousOn_price_image {A : Type*} [TopologicalSpace A] {I : Set A}
    (δ : Finset E → ℝ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsub : IntersectingSubmodular δ)
    (hpair : ∀ x ∈ C, ∀ y ∈ C, δ {x, y} = dist x y)
    (S : Finset ι) (hS : S.Nonempty) (f : ι → A → E)
    (hC : ∀ i ∈ S, ∀ t ∈ I, f i t ∈ C) (hf : ∀ i ∈ S, ContinuousOn (f i) I) :
    ContinuousOn (fun t => δ (S.image fun i => f i t)) I := by
  intro t ht
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (g := fun s => ∑ i ∈ S, dist (f i s) (f i t))
    (.of_forall fun _ => dist_nonneg)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact patchPrice_dist_le δ hmono hsub hpair S hS (fun i => f i s) (fun i => f i t)
      (fun i hi => hC i hi s hs) (fun i hi => hC i hi t ht)
  · simpa using tendsto_finsetSum S (fun i hi => tendsto_iff_dist_tendsto_zero.mp (hf i hi t ht))

end

end SpectralBooks
end LinearAlgebra
end OAI
