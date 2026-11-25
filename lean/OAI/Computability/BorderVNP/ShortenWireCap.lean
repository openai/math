import OAI.Computability.BorderVNP.ShortenCatalogStep

/-!
# The small wire-length cap is invariant across shortening rounds

The distance between the spatial chart and the corresponding geodesic at
radius `r` is at most `r` times the tangent norm. Thus the endpoint hook
and each interior cable stay within the old cap `2h` whenever the canonical
half-lengths lie in `[0,h]`. This same scale can be fixed before the epoch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Epoch Catalog CombiningStep
open scoped Classical

variable {I : Type*} [Fintype I]

/-- At every nonnegative radius, the chart-to-geodesic discrepancy costs
at most the radius times the full product tangent norm. -/
theorem product_hook_le_radius {r : ℝ} (hr : 0 ≤ r) (v : PiLp 2 (fun _ : I => ℂ)) :
    dist (productChart (r • v)) (productLine v r) ≤ r * ‖v‖ := by
  rw [← sq_le_sq₀ dist_nonneg (mul_nonneg hr (norm_nonneg _)), host_dist_sq, mul_pow,
    PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_pow]
  apply pow_le_pow_left₀ dist_nonneg
  have hi : 0 ≤ r * ‖v i‖ := mul_nonneg hr (norm_nonneg _)
  have hpt : (r * ‖v i‖) • unitDirection (v i) = r • v i := by
    rw [mul_smul, norm_smul_unitDirection]
  change dist (tangentChart (r • v i)) (tangentLine (unitDirection (v i)) (r * ‖v i‖)) ≤ _
  rw [← hpt,tangentChart_hook _ (unitDirection_norm _) hi]
  exact sub_le_self _ (Real.arsinh_nonneg_iff.mpr hi)

variable {D : ℕ}

/-- Two sites in the Euclidean unit ball install at distance at most one
full original segment length. -/
theorem SeedChart.atSite_dist (c : SeedChart I D) (hr : 0 ≤ c.radius)
    {u v : EuclideanSpace ℝ (Fin D)} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    dist (c.atSite u) (c.atSite v) ≤ 2*c.radius := by
  unfold atSite
  rw [(shiftTo_isometry c.center).dist_eq]
  refine (productChart_dist_le _ _).trans ?_
  rw [dist_smul₀,c.axes.isometry.dist_eq,Real.norm_eq_abs,abs_of_nonneg hr]
  have hlen : dist u v ≤ 2 := (dist_le_norm_add_norm _ _).trans (by linarith)
  exact (mul_le_mul_of_nonneg_left hlen hr).trans_eq (mul_comm _ _)

/-- Bound the discrepancy at an actual physical terminal. -/
theorem SeedChart.atTerminal_dist (c : SeedChart I D) (hr : 0 ≤ c.radius) (u : Fin D × Bool) :
    dist (c.atTerminal u) (c.atSite (antipodalPosition u)) ≤ c.radius := by
  unfold atTerminal atSite
  rw [(shiftTo_isometry c.center).dist_eq,dist_comm]
  refine (product_hook_le_radius hr _).trans (mul_le_of_le_one_right hr ?_)
  rw [c.axes.norm_map]
  rcases u with ⟨i,b⟩
  cases b <;> simp [antipodalPosition]

variable [NeZero D] {m : ℕ} {K : Type*} [Field K] {P : Type*} {bits : P → ℕ}
variable {A : Type} [Fintype A] {Q : Type*} [PseudoMetricSpace Q]

/-- A single cap `2h` is preserved by every actual joint histogram. The
endpoint tolerance can always be narrowed to `min ν 1`, in which case the
hypothesis `η ≤ 4` holds independently of the paid identity. -/
theorem preserved_wire_cap (e : PaidIdentity K D m) (p : Pack D P bits K)
    (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool)
    (g : Placement (m := m) p bin perm I Q) {η h : ℝ} (hη : η ≤ 4)
    (fits : g.fits p bin perm positive h η)
    (hret : ∀ c, (bin c).isSome = true → dist (g.old (p.layout.src c)) (g.old (p.layout.dst c)) ≤ 2*h)
    (q : Counts e p bin perm) :
    ∀ c : (physical p bin perm e positive q).Edge, postMask p bin perm e positive q c = true →
      let N := physical p bin perm e positive q
      let z := g.postSites p bin perm e positive q
      dist (z (N.src c)) (z (N.dst c)) ≤ 2*h := by
  let t := SeedIntervals.partition p.layout bin perm m
  let b := SeedIntervals.bundle p.layout bin perm m positive
  let j := SeedIntervals.blocks p.layout bin perm m
  let G := seedNetwork e j (p := pieces (m := m) p bin perm) t b q
  let up := fun a v => (g.chart a).atSite ((G a).position v)
  let down := fun a v => g.project a (up a v)
  apply t.edge_bound G g.old down (fun c => (bin c.1).isSome)
  · intro c hc; exact hret _ hc
  · intro a u
    rw [← g.projects a u]
    refine (g.nonexpanding a _ _).trans ?_
    let c := g.chart a
    have hterm : (G a).position ((G a).attach u) = antipodalPosition ((b a).terminal u) :=
      e.profile_placedAt (j a) (q a).val ((b a).terminal u)
    change dist (g.lift a u) (c.atSite ((G a).position ((G a).attach u))) ≤ 2*h
    rw [hterm]
    have hnear := fits.2 a u
    have hh := c.atTerminal_dist (fits.1 a).1 ((b a).terminal u)
    have hfrac : (η/4) * c.radius ≤ c.radius :=
      mul_le_of_le_one_left (fits.1 a).1 (by linarith)
    exact (dist_triangle _ (c.atTerminal ((b a).terminal u)) _).trans
      ((add_le_add (hnear.trans hfrac) hh).trans (by linarith only [(fits.1 a).2]))
  · intro a x
    refine (g.nonexpanding a _ _).trans ?_
    exact ((g.chart a).atSite_dist (fits.1 a).1 ((G a).in_ball ((G a).src x)) ((G a).in_ball ((G a).dst x))).trans
      (mul_le_mul_of_nonneg_left (fits.1 a).2 (by norm_num))

omit [Field K] [Fintype A] in
/-- Tightening the bin and hook tolerances preserves all conditions for the
original savings. -/
theorem CombiningStep.Placement.fits_mono (p : Pack D P bits K) (bin : p.layout.Edge → Option A)
    (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool)
    (g : Placement (m := m) p bin perm I Q) {h h' ν ν' : ℝ}
    (hh : h ≤ h') (hν : ν ≤ ν') (fits : g.fits p bin perm positive h ν) :
    g.fits p bin perm positive h' ν' :=
  ⟨fun a => ⟨(fits.1 a).1, (fits.1 a).2.trans hh⟩, fun a u =>
    (fits.2 a u).trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hν (by norm_num))
      (fits.1 a).1)⟩

end Shortening

end BorderVNP
end Computability
end OAI
