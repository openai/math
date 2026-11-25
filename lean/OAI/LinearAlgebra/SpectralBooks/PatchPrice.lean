import OAI.LinearAlgebra.SpectralBooks.PlacementConvexity
import OAI.LinearAlgebra.SpectralBooks.TangentPrice
import Mathlib.Analysis.Normed.Module.Basic

/-! # Prices on a Euclidean patch and their infinitesimal limits

The synchronized convexity inequality can be used within a bounded patch.
At an interior point every fixed finite configuration lies in the patch
after a sufficiently small dilation.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Filter Set
open scoped Classical Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Joint convexity of placed prices when all the endpoints belong to a patch. -/
def JointlyConvexPriceOn (C : Set E) (δ : Finset E → ℝ) : Prop :=
  ∀ (P : Finset (E × E)), P.Nonempty → (∀ p ∈ P, p.1 ∈ C ∧ p.2 ∈ C) →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      δ (P.image fun p ↦ a • p.1 + b • p.2) ≤
        a * δ (P.image Prod.fst) + b * δ (P.image Prod.snd)

/-- All rescaled finite prices at the same point have the specified limits. -/
def IsTangentPriceAt (δ : Finset E → ℝ) (y : E) (D : Finset E → ℝ) : Prop :=
  ∀ S : Finset E, S.Nonempty → Tendsto (fun h : ℝ ↦ δ (S.image (fun w ↦ y + h • w)) / h)
    (𝓝[>] 0) (𝓝 (D S))

theorem eventually_patch_image_subset {C : Set E} {y : E} (hy : y ∈ interior C) (S : Finset E) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), (S.image (fun w ↦ y + h • w) : Set E) ⊆ C := by
  have hx (x : E) : Tendsto (fun h : ℝ ↦ y + h • x) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
    have hc : Continuous (fun h : ℝ ↦ y + h • x) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  filter_upwards [(eventually_all_finset S).mpr fun x _ ↦ (hx x) (mem_interior_iff_mem_nhds.mp hy)]
    with h hh
  intro z hz
  obtain ⟨x, hx', rfl⟩ := Finset.mem_image.mp hz
  exact hh x hx'

/-- Synchronized interpolation specializes to convexity in the dilation parameter
on any interval for which the dilated sites stay in the patch. -/
theorem JointlyConvexPriceOn.convexOn_dilation {C : Set E} {δ : Finset E → ℝ}
    (hc : JointlyConvexPriceOn C δ) (S : Finset E) (hS : S.Nonempty) (y : E) {I : Set ℝ}
    (hI : Convex ℝ I) (hloc : ∀ t ∈ I, ∀ x ∈ S, y + t • x ∈ C) :
    ConvexOn ℝ I (fun t ↦ δ (S.image (fun x ↦ y + t • x))) := by
  refine ⟨hI, ?_⟩
  intro t ht s hs a b ha hb hab
  let P := S.image (fun x ↦ (y + t • x, y + s • x))
  have hP : ∀ p ∈ P, p.1 ∈ C ∧ p.2 ∈ C := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hloc t ht x hx, hloc s hs x hx⟩
  have h := hc P (hS.image _) hP a b ha hb hab
  have haff (x : E) : a • (y + t • x) + b • (y + s • x) = y + (a * t + b * s) • x := by
    rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul,
      hab, one_smul, add_smul]
  simpa only [P, Finset.image_image, Function.comp_def, haff, smul_eq_mul] using h

/-- The tangent price exists simultaneously on all finite configurations at an
interior point. Nonnegativity bounds the convex secant slopes from below. -/
theorem exists_tangentPriceAt {C : Set E} {δ : Finset E → ℝ} (hc : JointlyConvexPriceOn C δ)
    {y : E} (hy : y ∈ interior C) (hy0 : δ {y} = 0)
    (hnonneg : ∀ (S : Finset E), S.Nonempty → (S : Set E) ⊆ C → 0 ≤ δ S) :
    ∃ D : Finset E → ℝ, IsTangentPriceAt δ y D := by
  have hex (S : Finset E) (hS : S.Nonempty) :
      ∃ l : ℝ, 0 ≤ l ∧ Tendsto (fun h : ℝ ↦ δ (S.image (fun w ↦ y + h • w)) / h)
        (𝓝[>] 0) (𝓝 l) := by
    obtain ⟨R, hR, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (eventually_patch_image_subset hy S)
    have hI (t : ℝ) (ht : t ∈ Icc 0 R) : (S.image (fun x ↦ y + t • x) : Set E) ⊆ C := by
      rcases ht.1.eq_or_lt with h | h
      · subst t
        simpa [Finset.image_const hS] using interior_subset hy
      · exact hsub ⟨h, ht.2⟩
    apply exists_tangentPrice hR (hc.convexOn_dilation S hS y (convex_Icc _ _)
      (fun t ht x hx ↦ hI t ht (Finset.mem_image_of_mem _ hx)))
    · simpa [Finset.image_const hS] using hy0
    · exact fun t ht ↦ hnonneg _ (hS.image _) (hI t ht)
  refine ⟨fun S ↦ if hS : S.Nonempty then (hex S hS).choose else 0, ?_⟩
  intro S hS
  simpa [hS] using (hex S hS).choose_spec.2

end

end

end SpectralBooks
end LinearAlgebra
end OAI
