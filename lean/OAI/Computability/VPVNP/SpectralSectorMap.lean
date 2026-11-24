import OAI.Computability.VPVNP.WireGeodesic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Interpolation on a sector of the spectral wire geometry

Section 4.1 constructs a sector from two constant-speed segments or rays
whose distance at parameter `r` equals `c * r`. Equation (2.2) forces
affine interpolation of sector coordinates to trace a constant-speed segment.
Taking the radial parameter set to be `Icc 0 R` gives a triangle, and taking
it to be `Ici 0` gives the entire quadrant.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

variable {X : Type*} [PseudoMetricSpace X]

/-- Coordinates in the nonnegative quadrant with radius in `S`. -/
def sectorDomain (S : Set ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ∈ S}

/-- Convexity of the radial interval gives convexity of the sector. -/
theorem sectorDomain_convex {S : Set ℝ} (hS : Convex ℝ S) : Convex ℝ (sectorDomain S) := by
  intro p hp q hq u v hu hv huv
  refine ⟨add_nonneg (mul_nonneg hu hp.1) (mul_nonneg hv hq.1),
    add_nonneg (mul_nonneg hu hp.2.1) (mul_nonneg hv hq.2.1), ?_⟩
  change u*p.1+v*q.1 + (u*p.2+v*q.2) ∈ S
  rw [show u*p.1+v*q.1 + (u*p.2+v*q.2) = u*(p.1+p.2)+v*(q.1+q.2) by ring]
  exact hS hp.2.2 hq.2.2 hu hv huv

theorem sectorRatio_mem (p : ℝ × ℝ) (hp₁ : 0 ≤ p.1) (hp₂ : 0 ≤ p.2) :
    0 ≤ p.2 / (p.1 + p.2) ∧ p.2 / (p.1 + p.2) ≤ 1 :=
  ⟨div_nonneg hp₂ (add_nonneg hp₁ hp₂), div_le_one_of_le₀ (by linarith) (add_nonneg hp₁ hp₂)⟩

theorem sectorRatio_mul (p : ℝ × ℝ) (hp₁ : 0 ≤ p.1) (hp₂ : 0 ≤ p.2) :
    p.2 / (p.1 + p.2) * (p.1 + p.2) = p.2 := by
  by_cases h : p.1 + p.2 = 0
  · have : p.2 = 0 := by linarith
    simp [this]
  · exact div_mul_cancel₀ _ h

/-- The point at fraction `v / (u + v)` on the chord joining the two rays at radius `u + v`.
The total function is used only on its sector domain. -/
noncomputable def sectorPoint (hf : HasFractions X) (a b : ℝ → X) (p : ℝ × ℝ) : X :=
  if hp : 0 ≤ p.1 ∧ 0 ≤ p.2 then
    (hf (a (p.1 + p.2)) (b (p.1 + p.2)) (p.2 / (p.1 + p.2))
      (sectorRatio_mem p hp.1 hp.2).1 (sectorRatio_mem p hp.1 hp.2).2).choose
  else a 0

theorem sectorPoint_radial_fraction (hf : HasFractions X) (a b : ℝ → X) (p : ℝ × ℝ)
    (hp₁ : 0 ≤ p.1) (hp₂ : 0 ≤ p.2) :
    AtFraction (a (p.1 + p.2)) (b (p.1 + p.2)) (p.2 / (p.1 + p.2)) (sectorPoint hf a b p) := by
  rw [sectorPoint, dite_eq_left ⟨hp₁, hp₂⟩]
  exact Exists.choose_spec _

/-- Distances from the two ends of the chord at the given radius. -/
theorem sectorPoint_boundary_distances (hf : HasFractions X) (a b : ℝ → X)
    {S : Set ℝ} {c : ℝ} (hc : ∀ r ∈ S, dist (a r) (b r) = c * r)
    {p : ℝ × ℝ} (hp : p ∈ sectorDomain S) :
    dist (a (p.1 + p.2)) (sectorPoint hf a b p) = c * p.2 ∧
    dist (sectorPoint hf a b p) (b (p.1 + p.2)) = c * p.1 := by
  obtain ⟨h₁, h₂⟩ := sectorPoint_radial_fraction hf a b p hp.1 hp.2.1
  rw [hc _ hp.2.2] at h₁ h₂
  have he := sectorRatio_mul p hp.1 hp.2.1
  constructor <;> linarith only [h₁, h₂, congrArg (c * ·) he]

/-- The horizontal coordinate axis agrees, up to distance zero, with the first ray. -/
theorem sectorPoint_axis_left (hf : HasFractions X) (a b : ℝ → X)
    {S : Set ℝ} {c : ℝ} (hc : ∀ r ∈ S, dist (a r) (b r) = c * r)
    {r : ℝ} (hr : 0 ≤ r) (hS : r ∈ S) : dist (a r) (sectorPoint hf a b (r, 0)) = 0 := by
  have hp : (r, 0) ∈ sectorDomain S := ⟨hr, le_rfl, by simpa using hS⟩
  simpa using (sectorPoint_boundary_distances hf a b hc hp).1

/-- The vertical coordinate axis agrees, up to distance zero, with the second ray. -/
theorem sectorPoint_axis_right (hf : HasFractions X) (a b : ℝ → X)
    {S : Set ℝ} {c : ℝ} (hc : ∀ r ∈ S, dist (a r) (b r) = c * r)
    {r : ℝ} (hr : 0 ≤ r) (hS : r ∈ S) : dist (sectorPoint hf a b (0, r)) (b r) = 0 := by
  have hp : (0, r) ∈ sectorDomain S := ⟨le_rfl, hr, by simpa using hS⟩
  simpa using (sectorPoint_boundary_distances hf a b hc hp).2

/-- A constant-speed boundary ray carries affine combinations of parameters to fractions. -/
private theorem ray_fraction {S : Set ℝ} {a : ℝ → X} {A : ℝ}
    (ha : ∀ r ∈ S, ∀ s ∈ S, dist (a r) (a s) = A * |r - s|)
    {r s t : ℝ} (hr : r ∈ S) (hs : s ∈ S) (hm : (1 - t) * r + t * s ∈ S)
    (ht : 0 ≤ t) (ht' : t ≤ 1) :
    AtFraction (a r) (a s) t (a ((1-t)*r+t*s)) := by
  constructor
  · rw [ha _ hr _ hm, ha _ hr _ hs, show r - ((1-t)*r+t*s) = t*(r-s) by ring,
      abs_mul, abs_of_nonneg ht]
    ring
  · rw [ha _ hm _ hs, ha _ hr _ hs, show (1-t)*r+t*s - s = (1-t)*(r-s) by ring,
      abs_mul, abs_of_nonneg (sub_nonneg.mpr ht')]
    ring

/-- Interpolating the coordinates of any two points in the sector interpolates their
images at the same fraction. This applies to both boundary and interior points. -/
theorem sectorPoint_atFraction (hf : HasFractions X) (hT : FractionTransport X)
    {a b : ℝ → X} {A B c : ℝ} {S : Set ℝ} (hS : Convex ℝ S)
    (ha : ∀ r ∈ S, ∀ s ∈ S, dist (a r) (a s) = A * |r - s|)
    (hb : ∀ r ∈ S, ∀ s ∈ S, dist (b r) (b s) = B * |r - s|)
    (hc : ∀ r ∈ S, dist (a r) (b r) = c * r)
    {p q : ℝ × ℝ} (hp : p ∈ sectorDomain S) (hq : q ∈ sectorDomain S)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    AtFraction (sectorPoint hf a b p) (sectorPoint hf a b q) t
      (sectorPoint hf a b ((1-t) • p + t • q)) := by
  let v := (1-t) • p + t • q
  have v₁ : v.1 = (1-t)*p.1+t*q.1 := rfl
  have v₂ : v.2 = (1-t)*p.2+t*q.2 := rfl
  have vr : v.1+v.2 = (1-t)*(p.1+p.2)+t*(q.1+q.2) := by rw [v₁, v₂]; ring
  have h₀ : 0 ≤ 1-t := sub_nonneg.mpr ht'
  have hm := hS hp.2.2 hq.2.2 h₀ ht (show 1-t+t = 1 by ring)
  have hv : v ∈ sectorDomain S :=
    ⟨add_nonneg (mul_nonneg h₀ hp.1) (mul_nonneg ht hq.1),
     add_nonneg (mul_nonneg h₀ hp.2.1) (mul_nonneg ht hq.2.1), vr ▸ hm⟩
  have hva := ray_fraction ha hp.2.2 hq.2.2 hm ht ht'
  have hvb := ray_fraction hb hp.2.2 hq.2.2 hm ht ht'
  rw [← vr] at hva hvb
  obtain ⟨w, hw⟩ := hf (sectorPoint hf a b p) (sectorPoint hf a b q) t ht ht'
  have hu := hT ht ht' hva hw
  have hz := hT ht ht' hw hvb
  obtain ⟨hap, hbp⟩ := sectorPoint_boundary_distances hf a b hc hp
  obtain ⟨haq, hbq⟩ := sectorPoint_boundary_distances hf a b hc hq
  rw [hap, haq] at hu
  rw [hbp, hbq] at hz
  have htri := dist_triangle (a (v.1 + v.2)) w (b (v.1 + v.2))
  rw [hc _ hv.2.2] at htri
  have hwf : AtFraction (a (v.1+v.2)) (b (v.1+v.2)) (v.2/(v.1+v.2)) w := by
    have hu' : dist (a (v.1+v.2)) w ≤ c*v.2 := hu.trans_eq (by rw [v₂]; ring)
    have hz' : dist w (b (v.1+v.2)) ≤ c*v.1 := hz.trans_eq (by rw [v₁]; ring)
    have hmul := congrArg (c * ·) (sectorRatio_mul v hv.1 hv.2.1)
    constructor <;> rw [hc _ hv.2.2] <;> linarith only [hu', hz', htri, hmul]
  have hrat := sectorRatio_mem v hv.1 hv.2.1
  have hwH := hwf.dist_eq_zero_of_transport hT hrat.1 hrat.2
    (sectorPoint_radial_fraction hf a b v hv.1 hv.2.1)
  constructor
  · exact (PseudoMetricSpace.dist_eq_of_dist_zero _ hwH).symm.trans hw.1
  · rw [dist_comm]
    exact (PseudoMetricSpace.dist_eq_of_dist_zero _ hwH).symm.trans ((dist_comm _ _).trans hw.2)

/-- Exact distance between two fractions of the same chord, before passing to the metric
quotient. -/
private theorem chord_distance_of_le (hf : HasFractions X) (hT : FractionTransport X)
    {a b x y : X} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1)
    (hx : AtFraction a b s x) (hy : AtFraction a b t y) :
    dist x y = (t - s) * dist a b := by
  let k := s / t
  have hk : 0 ≤ k := div_nonneg hs (hs.trans hst)
  have hk' : k ≤ 1 := div_le_one_of_le₀ hst (hs.trans hst)
  have hkt : k * t = s := by
    by_cases h : t = 0
    · have : s = 0 := by linarith
      simp [k, h, this]
    · exact div_mul_cancel₀ _ h
  obtain ⟨w, hw⟩ := hf a y k hk hk'
  have haw : dist a w = s * dist a b := by rw [hw.1, hy.1, ← mul_assoc, hkt]
  have hwy : dist w y = (t-s) * dist a b := by
    rw [hw.2, hy.1]
    linarith only [congrArg (· * dist a b) hkt]
  have hwb : AtFraction a b s w := by
    refine ⟨haw, ?_⟩
    linarith only [haw, hwy, hy.2, dist_triangle a w b, dist_triangle w y b]
  have hzero := hx.dist_eq_zero_of_transport hT hs (hst.trans ht) hwb
  rw [dist_comm x y, PseudoMetricSpace.dist_eq_of_dist_zero y hzero, dist_comm y w, hwy]

theorem AtFraction.chord_distance (hf : HasFractions X) (hT : FractionTransport X)
    {a b x y : X} {s t : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hx : AtFraction a b s x) (hy : AtFraction a b t y) :
    dist x y = |s-t| * dist a b := by
  rcases le_total s t with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    exact chord_distance_of_le hf hT hs h ht' hx hy
  · rw [dist_comm x y, abs_of_nonneg (sub_nonneg.mpr h)]
    exact chord_distance_of_le hf hT ht h hs' hy hx

/-- A uniform continuity estimate comparing two slices. In particular it has no denominator
at the vertex of the sector. -/
theorem sectorPoint_distance_le (hf : HasFractions X) (hT : FractionTransport X)
    {a b : ℝ → X} {A B c : ℝ} {S : Set ℝ}
    (ha : ∀ r ∈ S, ∀ s ∈ S, dist (a r) (a s) = A * |r - s|)
    (hb : ∀ r ∈ S, ∀ s ∈ S, dist (b r) (b s) = B * |r - s|)
    (hc : ∀ r ∈ S, dist (a r) (b r) = c * r)
    {p q : ℝ × ℝ} (hp : p ∈ sectorDomain S) (hq : q ∈ sectorDomain S) :
    dist (sectorPoint hf a b p) (sectorPoint hf a b q) ≤
      (max A B + |c|) * |(p.1+p.2) - (q.1+q.2)| + |c| * |p.2-q.2| := by
  let r := p.1+p.2
  let R := q.1+q.2
  let s := p.2/r
  let t := q.2/R
  have hs := sectorRatio_mem p hp.1 hp.2.1
  have ht := sectorRatio_mem q hq.1 hq.2.1
  have hsr : s*r = p.2 := sectorRatio_mul p hp.1 hp.2.1
  have htR : t*R = q.2 := sectorRatio_mul q hq.1 hq.2.1
  have hR : 0 ≤ R := add_nonneg hq.1 hq.2.1
  obtain ⟨w, hw⟩ := hf (a R) (b R) s hs.1 hs.2
  have hrad := hT hs.1 hs.2 (sectorPoint_radial_fraction hf a b p hp.1 hp.2.1) hw
  rw [ha _ hp.2.2 _ hq.2.2, hb _ hp.2.2 _ hq.2.2] at hrad
  have hrad' : dist (sectorPoint hf a b p) w ≤ max A B * |r-R| := by
    apply hrad.trans
    change (1-s) * (A * |r-R|) + s * (B * |r-R|) ≤ _
    rw [← mul_assoc, ← mul_assoc, ← add_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    linarith only [mul_le_mul_of_nonneg_left (le_max_left A B) (sub_nonneg.mpr hs.2),
      mul_le_mul_of_nonneg_left (le_max_right A B) hs.1]
  have hchord := hw.chord_distance hf hT hs.1 hs.2 ht.1 ht.2
    (sectorPoint_radial_fraction hf a b q hq.1 hq.2.1)
  rw [hc _ hq.2.2] at hchord
  change dist w (sectorPoint hf a b q) = |s-t| * (c*R) at hchord
  have hrat : |s-t| * R ≤ |r-R| + |p.2-q.2| := by
    calc
      |s-t| * R = |s*R-t*R| := by rw [← sub_mul, abs_mul, abs_of_nonneg hR]
      _ ≤ |s*R-s*r| + |s*r-t*R| := abs_sub_le _ _ _
      _ = s*|r-R| + |p.2-q.2| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hs.1, abs_sub_comm R r, hsr, htR]
      _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_right hs.2 (abs_nonneg (r-R))]
  have hchord' : dist w (sectorPoint hf a b q) ≤ |c| * (|r-R|+|p.2-q.2|) := by
    calc
      _ = c * (|s-t| * R) := by rw [hchord]; ring
      _ ≤ |c| * (|s-t| * R) := mul_le_mul_of_nonneg_right (le_abs_self c)
        (mul_nonneg (abs_nonneg _) hR)
      _ ≤ _ := mul_le_mul_of_nonneg_left hrat (abs_nonneg _)
  change _ ≤ (max A B + |c|)*|r-R| + |c| *|p.2-q.2|
  linarith only [dist_triangle (sectorPoint hf a b p) w (sectorPoint hf a b q), hrad', hchord']

/-- The sector map is continuous on the closed triangle or quadrant, including its vertex. -/
theorem sectorPoint_continuousOn (hf : HasFractions X) (hT : FractionTransport X)
    {a b : ℝ → X} {A B c : ℝ} {S : Set ℝ}
    (ha : ∀ r ∈ S, ∀ s ∈ S, dist (a r) (a s) = A * |r - s|)
    (hb : ∀ r ∈ S, ∀ s ∈ S, dist (b r) (b s) = B * |r - s|)
    (hc : ∀ r ∈ S, dist (a r) (b r) = c * r) :
    ContinuousOn (sectorPoint hf a b) (sectorDomain S) := by
  intro q hq
  apply tendsto_iff_dist_tendsto_zero.mpr
  let g (p : ℝ × ℝ) := (max A B + |c|) * |(p.1+p.2) - (q.1+q.2)| + |c| * |p.2-q.2|
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ dist_nonneg) (g := g)
  · exact Filter.Eventually.mono self_mem_nhdsWithin fun _ hp ↦
      sectorPoint_distance_le hf hT ha hb hc hp hq
  · have hg : Continuous g := by unfold g; fun_prop
    simpa [g] using (hg.continuousWithinAt (s := sectorDomain S) (x := q)).tendsto

end WireGeometry

end VPVNP
end Computability
end OAI
