import OAI.LinearAlgebra.SpectralBooks.Sector
import OAI.LinearAlgebra.SpectralBooks.SectorTriangleSeminorm

/-! # The seminorm on the parameter triangle of a bounded sector -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open HyperbolicObstruction Set

/-- Convex radius ranges give convex sector domains. -/
theorem convex_sectorDomain {D : Set ℝ} (hD : Convex ℝ D) : Convex ℝ (sectorDomain D) := by
  intro p hp q hq a b ha hb hab
  refine ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1),
    add_nonneg (mul_nonneg ha hp.2.1) (mul_nonneg hb hq.2.1), ?_⟩
  change (a*p.1+b*q.1)+(a*p.2+b*q.2) ∈ D
  rw [show (a*p.1+b*q.1)+(a*p.2+b*q.2) = a*(p.1+p.2)+b*(q.1+q.2) by ring]
  exact hD hp.2.2 hq.2.2 ha hb hab

/-- Every positive-radius sector triangle contains an open rectangle. -/
theorem sectorDomain_Icc_interior_nonempty {R : ℝ} (hR : 0 < R) :
    (interior (sectorDomain (Icc 0 R))).Nonempty := by
  let U := Ioo 0 (R/2) ×ˢ Ioo 0 (R/2)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hsub : U ⊆ sectorDomain (Icc 0 R) := by
    intro p hp
    obtain ⟨⟨hx,hx'⟩,hy,hy'⟩ := hp
    exact ⟨hx.le, hy.le, add_nonneg hx.le hy.le, by linarith⟩
  refine ⟨(R/4,R/4), interior_maximal hsub hU ?_⟩
  have hquarter : R/4 ∈ Ioo 0 (R/2) := ⟨by linarith, by linarith⟩
  exact ⟨hquarter, hquarter⟩

variable {X : Type*} [MetricSpace X]

/-- Distances in the bounded sector, including its edges, are given by a single seminorm. -/
theorem sectorMap_triangle_seminorm (g : IsGeodesic X) (hB : SectorBusemann X)
    {a b : ℝ → X} {A B c R : ℝ} (hR : 0 < R)
    (ha : ∀ r ∈ Icc 0 R, ∀ s ∈ Icc 0 R, dist (a r) (a s) = |r-s| * A)
    (hb : ∀ r ∈ Icc 0 R, ∀ s ∈ Icc 0 R, dist (b r) (b s) = |r-s| * B)
    (hsep : ∀ r ∈ Icc 0 R, dist (a r) (b r) = c*r) :
    ∃ N : Seminorm ℝ (ℝ × ℝ), ∀ p ∈ sectorDomain (Icc 0 R), ∀ q ∈ sectorDomain (Icc 0 R),
      dist (sectorMap g a b p) (sectorMap g a b q) = N (p-q) := by
  let H := sectorMap g a b
  have hfrac {p q : ℝ × ℝ} (hp : p ∈ sectorDomain (Icc 0 R))
      (hq : q ∈ sectorDomain (Icc 0 R)) {t : ℝ} (ht : t ∈ Icc 0 1) :
      SectorFraction (H p) (H q) (H ((1-t) • p + t • q)) t := by
    change SectorFraction _ _ (sectorMap g a b _) _
    rw [sectorMap_affine g hB (convex_Icc _ _) ha hb hsep hp hq ht]
    exact sectorSegment_fraction g _ _ ht
  apply convex_seminorm_of_affine (convex_sectorDomain (convex_Icc _ _))
    (sectorDomain_Icc_interior_nonempty hR) H
  · exact fun _ hp _ hq _ ht ↦ (hfrac hp hq ht).1
  · intro z hz p hp q hq t ht
    simpa using hB _ _ _ _ _ _ t ht (hfrac hz hp ht) (hfrac hz hq ht)

end SpectralBooks
end LinearAlgebra
end OAI
