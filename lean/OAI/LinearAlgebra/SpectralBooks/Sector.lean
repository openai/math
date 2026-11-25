import OAI.Geometry.HyperbolicGroups.Basic
import Mathlib.Tactic

/-!
# Affine segments in a sector

For two constant-speed paths with exactly linear separation from one another,
interpolate between their equal-radius points as in the sector construction in
`curvature.tex`. Busemann convexity forces all parameter segments of this map
to be constant-speed geodesics. The radius domain may be a bounded interval
or the whole nonnegative half-line.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open HyperbolicObstruction Set

variable {X : Type*} [MetricSpace X]

/-- Metric characterization of the point at parameter `t` on a segment. -/
def SectorFraction (a b z : X) (t : ℝ) : Prop :=
  dist a z = t * dist a b ∧ dist z b = (1-t) * dist a b

/-- Busemann convexity in its metric-fraction form. -/
def SectorBusemann (X : Type*) [MetricSpace X] : Prop :=
  ∀ a b a' b' z w : X, ∀ t ∈ Icc (0 : ℝ) 1,
    SectorFraction a b z t → SectorFraction a' b' w t →
    dist z w ≤ (1-t) * dist a a' + t * dist b b'

/-- Choose a metric segment in the geodesic space. -/
noncomputable def sectorSegment (g : IsGeodesic X) (a b : X) : ℝ → X := (g a b).choose

theorem sectorSegment_fraction (g : IsGeodesic X) (a b : X) {t : ℝ} (ht : t ∈ Icc 0 1) :
    SectorFraction a b (sectorSegment g a b t) t := by
  have h : IsSegment (sectorSegment g a b) a b := (g a b).choose_spec
  constructor
  · calc
      dist a _ = dist (sectorSegment g a b 0) (sectorSegment g a b t) := by rw [h.1]
      _ = _ := by simpa [abs_of_nonneg ht.1] using h.2.2 0 (by norm_num) t ht
  · calc
      dist _ b = dist (sectorSegment g a b t) (sectorSegment g a b 1) := by rw [h.2.1]
      _ = _ := by simpa [abs_of_nonpos (sub_nonpos.mpr ht.2)] using h.2.2 t ht 1 (by norm_num)

theorem SectorBusemann.fraction_unique (hB : SectorBusemann X) {a b z w : X} {t : ℝ}
    (ht : t ∈ Icc 0 1) (hz : SectorFraction a b z t) (hw : SectorFraction a b w t) :
    z = w := by
  exact dist_le_zero.mp (by simpa using hB a b a b z w t ht hz hw)

/-- Parameter domain of the sector with allowable radii `D`. -/
def sectorDomain (D : Set ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ∈ D}

private theorem sectorRatio_mem {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    v / (u+v) ∈ Icc 0 1 := by
  rcases eq_or_lt_of_le (add_nonneg hu hv) with h | h
  · simp [← h]
  exact ⟨div_nonneg hv h.le, (div_le_one h).mpr (by linarith)⟩

/-- The manuscript's sector map. At the origin the parameter `0/0` is zero. -/
noncomputable def sectorMap (g : IsGeodesic X) (a b : ℝ → X) (p : ℝ × ℝ) : X :=
  sectorSegment g (a (p.1+p.2)) (b (p.1+p.2)) (p.2/(p.1+p.2))

/-- Distances to the two boundary rays at the radius of a sector point. -/
theorem sectorMap_boundary_dist (g : IsGeodesic X) {a b : ℝ → X} {D : Set ℝ} {c : ℝ}
    (hsep : ∀ r ∈ D, dist (a r) (b r) = c*r) {p : ℝ × ℝ} (hp : p ∈ sectorDomain D) :
    dist (a (p.1+p.2)) (sectorMap g a b p) = c*p.2 ∧
    dist (sectorMap g a b p) (b (p.1+p.2)) = c*p.1 := by
  obtain ⟨hu, hv, hD⟩ := hp
  obtain ⟨ha, hb⟩ := sectorSegment_fraction g (a (p.1+p.2)) (b (p.1+p.2))
    (sectorRatio_mem hu hv)
  change dist _ (sectorMap g a b p) = _ at ha
  change dist (sectorMap g a b p) _ = _ at hb
  rw [hsep _ hD] at ha hb
  rcases eq_or_lt_of_le (add_nonneg hu hv) with h | h
  · have hu0 : p.1 = 0 := by linarith
    have hv0 : p.2 = 0 := by linarith
    simpa [hu0, hv0] using And.intro ha hb
  · constructor
    · rw [ha]
      field_simp
    · rw [hb]
      field_simp
      ring

/-- Constant-speed paths parametrized by radius take affine parameters to metric fractions. -/
private theorem radial_fraction {a : ℝ → X} {D : Set ℝ} {A : ℝ}
    (ha : ∀ r ∈ D, ∀ s ∈ D, dist (a r) (a s) = |r-s| * A)
    {r s t : ℝ} (hr : r ∈ D) (hs : s ∈ D) (ht : t ∈ Icc 0 1)
    (hi : (1-t)*r+t*s ∈ D) :
    SectorFraction (a r) (a s) (a ((1-t)*r+t*s)) t := by
  constructor
  · rw [ha _ hr _ hi, ha _ hr _ hs, show r-((1-t)*r+t*s) = t*(r-s) by ring,
      abs_mul, abs_of_nonneg ht.1]
    ring
  · rw [ha _ hi _ hs, ha _ hr _ hs, show (1-t)*r+t*s-s = (1-t)*(r-s) by ring,
      abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    ring

/-- The sector map intertwines affine interpolation with geodesic interpolation. -/
theorem sectorMap_affine (g : IsGeodesic X) (hB : SectorBusemann X)
    {a b : ℝ → X} {D : Set ℝ} (hD : Convex ℝ D) {A B c : ℝ}
    (ha : ∀ r ∈ D, ∀ s ∈ D, dist (a r) (a s) = |r-s| * A)
    (hb : ∀ r ∈ D, ∀ s ∈ D, dist (b r) (b s) = |r-s| * B)
    (hsep : ∀ r ∈ D, dist (a r) (b r) = c*r)
    {p q : ℝ × ℝ} (hp : p ∈ sectorDomain D) (hq : q ∈ sectorDomain D)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    sectorMap g a b ((1-t) • p + t • q) =
      sectorSegment g (sectorMap g a b p) (sectorMap g a b q) t := by
  let k := (1-t) • p + t • q
  let w := sectorSegment g (sectorMap g a b p) (sectorMap g a b q) t
  have hw : SectorFraction (sectorMap g a b p) (sectorMap g a b q) w t :=
    sectorSegment_fraction g _ _ ht
  have hk₁ : k.1 = (1-t)*p.1+t*q.1 := rfl
  have hk₂ : k.2 = (1-t)*p.2+t*q.2 := rfl
  have hr : k.1+k.2 = (1-t)*(p.1+p.2)+t*(q.1+q.2) := by rw [hk₁, hk₂]; ring
  have ht' := sub_nonneg.mpr ht.2
  have hsum : (1-t)*(p.1+p.2)+t*(q.1+q.2) ∈ D :=
    hD hp.2.2 hq.2.2 ht' ht.1 (by ring)
  have hk : k ∈ sectorDomain D := ⟨add_nonneg (mul_nonneg ht' hp.1) (mul_nonneg ht.1 hq.1),
    add_nonneg (mul_nonneg ht' hp.2.1) (mul_nonneg ht.1 hq.2.1), hr ▸ hsum⟩
  have hp' := sectorMap_boundary_dist g hsep hp
  have hq' := sectorMap_boundary_dist g hsep hq
  have hleft := hB _ _ _ _ _ _ t ht (radial_fraction ha hp.2.2 hq.2.2 ht hsum) hw
  have hright := hB _ _ _ _ _ _ t ht hw (radial_fraction hb hp.2.2 hq.2.2 ht hsum)
  rw [←hr, hp'.1, hq'.1] at hleft
  rw [←hr, hp'.2, hq'.2] at hright
  rw [show (1-t)*(c*p.2)+t*(c*q.2) = c*k.2 by rw [hk₂]; ring] at hleft
  rw [show (1-t)*(c*p.1)+t*(c*q.1) = c*k.1 by rw [hk₁]; ring] at hright
  have htr := dist_triangle (a (k.1+k.2)) w (b (k.1+k.2))
  rw [hsep _ hk.2.2] at htr
  have hval := sectorMap_boundary_dist g hsep hk
  have hfra := sectorSegment_fraction g (a (k.1+k.2)) (b (k.1+k.2)) (sectorRatio_mem hk.1 hk.2.1)
  apply hB.fraction_unique (sectorRatio_mem hk.1 hk.2.1) hfra
  constructor
  · rw [←hfra.1]
    change dist _ w = dist _ (sectorMap g a b k)
    rw [hval.1]
    linarith only [hleft, hright, htr]
  · rw [←hfra.2]
    change dist w _ = dist (sectorMap g a b k) _
    rw [hval.2]
    linarith only [hleft, hright, htr]

/-- Restrictions of the sector map to the two coordinate axes. -/
theorem sectorMap_axes (g : IsGeodesic X) {a b : ℝ → X} {D : Set ℝ} {c r : ℝ}
    (hsep : ∀ s ∈ D, dist (a s) (b s) = c*s) (hr : 0 ≤ r) (hrD : r ∈ D) :
    sectorMap g a b (r,0) = a r ∧ sectorMap g a b (0,r) = b r := by
  have h₁ := (sectorMap_boundary_dist g hsep (p := (r,0)) ⟨hr, le_rfl, by simpa⟩).1
  have h₂ := (sectorMap_boundary_dist g hsep (p := (0,r)) ⟨le_rfl, hr, by simpa⟩).2
  constructor
  · exact (dist_eq_zero.mp (by simpa using h₁)).symm
  · exact dist_eq_zero.mp (by simpa using h₂)

end SpectralBooks
end LinearAlgebra
end OAI
