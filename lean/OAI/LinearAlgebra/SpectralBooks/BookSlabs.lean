import OAI.LinearAlgebra.SpectralBooks.BookDilation
import OAI.LinearAlgebra.SpectralBooks.FacetCube

/-!
# The bounded book in a doubled cube

The common upper facet supplies the spine. Its inward slab lies in both charts,
and each chart supplies a separate outward slab. Their cross-distance formula
identifies the metric on their union with the metric on the bounded book.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open Set
open scoped NNReal

variable {ι X : Type*} [Fintype ι] [MetricSpace X]

/-- Coordinates at signed height `t` over the facet with normal axis `none`. -/
private def slabCoordinates (p : EuclideanSpace ℝ ι) (t : ℝ) : EuclideanSpace ℝ (Option ι) :=
  WithLp.toLp 2 (fun j ↦ j.elim (1 + t) p)

private theorem slabCoordinates_dist_sq (p q : EuclideanSpace ℝ ι) (r s : ℝ) :
    dist (slabCoordinates p r) (slabCoordinates q s) ^ 2 =
      (r - s) ^ 2 + dist p q ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fintype.sum_option, EuclideanSpace.dist_sq_eq]
  change dist (1 + r) (1 + s) ^ 2 + _ = _
  rw [Real.dist_eq, add_sub_add_left_eq_sub, sq_abs]
  rfl

private theorem slabCoordinates_in_cube {p : EuclideanSpace ℝ ι} (hp : ‖p‖ ≤ 1)
    {a t : ℝ} (ha : 1 ≤ a) (ht : 1 + t ∈ Icc (-a) a) :
    slabCoordinates p t ∈ coordinateCube (Option ι) a := by
  rintro (_ | j)
  · exact ht
  · have h : |p j| ≤ a := by
      rw [← Real.norm_eq_abs]
      exact (PiLp.norm_apply_le p j).trans (hp.trans ha)
    exact abs_le.mp h

private theorem slabCoordinates_facet {p : EuclideanSpace ℝ ι} (hp : ‖p‖ ≤ 1) :
    slabCoordinates p 0 ∈ upperUnitCubeFacet none :=
  ⟨slabCoordinates_in_cube hp le_rfl (by norm_num), by change 1 + 0 = (1 : ℝ); ring⟩

variable [DecidableEq ι]

omit [Fintype ι] in
private theorem slabCoordinates_translate (p : EuclideanSpace ℝ ι) (t : ℝ) :
    slabCoordinates p 0 + t • EuclideanSpace.single none 1 = slabCoordinates p t := by
  apply PiLp.ext
  rintro (_ | j) <;> simp [slabCoordinates, PiLp.add_apply, PiLp.smul_apply]

private def slabPage (b c : EuclideanSpace ℝ (Option ι) → X) (i : Fin 3)
    (r : ℝ≥0) (p : EuclideanSpace ℝ ι) : X :=
  if i = 0 then b (slabCoordinates p (-r)) else if i = 1 then b (slabCoordinates p r)
  else c (slabCoordinates p r)

/-- Two isometric doubled cubes agreeing on their unit cube contain a unit
three-page book whenever their outward slabs have the reflected Euclidean
cross distances. -/
theorem exists_isometry_boundedBook_of_cross_distances {b c : EuclideanSpace ℝ (Option ι) → X}
    (hb : ∀ u ∈ coordinateCube _ 2, ∀ v ∈ coordinateCube _ 2, dist (b u) (b v) = dist u v)
    (hc : ∀ u ∈ coordinateCube _ 2, ∀ v ∈ coordinateCube _ 2, dist (c u) (c v) = dist u v)
    (hbc : (coordinateCube _ 1).EqOn b c)
    (hcross : ∀ {p q : EuclideanSpace ℝ (Option ι)}, p ∈ upperUnitCubeFacet none →
      q ∈ upperUnitCubeFacet none → ∀ {r s : ℝ}, r ∈ Icc 0 1 → s ∈ Icc 0 1 →
      dist (b (p + r • EuclideanSpace.single none 1)) (c (q + s • EuclideanSpace.single none 1)) ^ 2 =
        dist p q ^ 2 + (r + s) ^ 2) :
    ∃ f : boundedBook (EuclideanSpace ℝ ι) → X, Isometry f := by
  have repr (x : boundedBook (EuclideanSpace ℝ ι)) :
      ∃ i r, bookPoint i r x.val.snd = x.val := by
    obtain ⟨i, r, hir⟩ := x.val.fst.property
    exact ⟨i, r, (WithLp.equiv 2 _).injective (Prod.ext (Subtype.ext hir.symm) rfl)⟩
  choose i r hir using repr
  have mem (x : boundedBook (EuclideanSpace ℝ ι)) :
      r x ≤ 1 ∧ ‖x.val.snd‖ ≤ 1 := by
    apply (bookPoint_mem_boundedBook _ _ _).mp
    rw [hir]
    exact x.property
  have outward (p : EuclideanSpace ℝ ι) (hp : ‖p‖ ≤ 1) (h : ℝ≥0) (hh : h ≤ 1) :
      slabCoordinates p h ∈ coordinateCube _ 2 ∧
      slabCoordinates p (-(h : ℝ)) ∈ coordinateCube _ 2 ∧
      slabCoordinates p (-(h : ℝ)) ∈ coordinateCube _ 1 := by
    have hle : (h : ℝ) ≤ 1 := hh
    have hge := h.property
    refine ⟨slabCoordinates_in_cube hp (by norm_num) ?_,
      slabCoordinates_in_cube hp (by norm_num) ?_, slabCoordinates_in_cube hp le_rfl ?_⟩ <;>
      constructor <;> linarith
  have bc (p q : EuclideanSpace ℝ ι) (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1)
      (r s : ℝ≥0) (hr : r ≤ 1) (hs : s ≤ 1) :
      dist (b (slabCoordinates p r)) (c (slabCoordinates q s)) ^ 2 =
        ((r : ℝ) + s) ^ 2 + dist p q ^ 2 := by
    have h := hcross (slabCoordinates_facet hp) (slabCoordinates_facet hq)
      (show (r : ℝ) ∈ Icc 0 1 from ⟨r.property, hr⟩)
      (show (s : ℝ) ∈ Icc 0 1 from ⟨s.property, hs⟩)
    simpa only [slabCoordinates_translate, slabCoordinates_dist_sq, sub_self, zero_pow (by decide : 2 ≠ 0),
      zero_add, add_comm] using h
  refine ⟨fun x ↦ slabPage b c (i x) (r x) x.val.snd, Isometry.of_dist_eq fun x y ↦ ?_⟩
  set p := x.val.snd
  set q := y.val.snd
  let a := r x
  let d := r y
  have hX := outward p (mem x).2 a (mem x).1
  have hY := outward q (mem y).2 d (mem y).1
  have hD : dist x y = Real.sqrt
      ((if i x = i y then |(a : ℝ) - d| else (a : ℝ) + d) ^ 2 + dist p q ^ 2) :=
    (show dist x y = dist (bookPoint (i x) a p) (bookPoint (i y) d q) by rw [hir, hir]; rfl).trans
      (book_dist _ _ _ _ _ _)
  rw [hD, ← Real.sqrt_sq (dist_nonneg (x := slabPage b c (i x) a p)
    (y := slabPage b c (i y) d q))]
  congr 1
  have hinX := hbc hX.2.2
  have hinY := hbc hY.2.2
  have hcrossXY := bc p q (mem x).2 (mem y).2 a d (mem x).1 (mem y).1
  have hcrossYX := bc q p (mem y).2 (mem x).2 d a (mem y).1 (mem x).1
  rw [dist_comm (b _), dist_comm q p, add_comm (d : ℝ)] at hcrossYX
  generalize i x = ix, i y = iy
  fin_cases ix <;> fin_cases iy <;> norm_num [slabPage, sq_abs] <;> first
    | exact hcrossXY
    | exact hcrossYX
    | rw [hb _ hX.1 _ hY.1, slabCoordinates_dist_sq]
    | rw [hc _ hX.1 _ hY.1, slabCoordinates_dist_sq]
    | rw [hb _ hX.2.1 _ hY.2.1, slabCoordinates_dist_sq]; ring
    | rw [hb _ hX.2.1 _ hY.1, slabCoordinates_dist_sq]; ring
    | rw [hb _ hX.1 _ hY.2.1, slabCoordinates_dist_sq]; ring
    | rw [hinX, hc _ hX.2.1 _ hY.1, slabCoordinates_dist_sq]; ring
    | rw [hinY, hc _ hX.1 _ hY.2.1, slabCoordinates_dist_sq]; ring

end

end

end SpectralBooks
end LinearAlgebra
end OAI
