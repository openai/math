import OAI.LinearAlgebra.SpectralBooks.MinkowskiSupport
import OAI.LinearAlgebra.SpectralBooks.TriangleWidth
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! The finite planar configurations used for the anchor and satellite rules. -/

noncomputable section
open scoped Classical Pointwise
open OAI.LinearAlgebra.SpectralBooks

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Planar

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def xy (x y : ℝ) : Plane := WithLp.toLp 2 ![x,y]

@[simp] theorem xy_zero (x y : ℝ) : xy x y 0 = x := rfl
@[simp] theorem xy_one (x y : ℝ) : xy x y 1 = y := rfl

@[simp] theorem xy_eq_iff {x y x' y' : ℝ} : xy x y = xy x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    exact ⟨congrArg (fun p : Plane ↦ p 0) h, congrArg (fun p : Plane ↦ p 1) h⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem xy_add (x y u v : ℝ) : xy x y + xy u v = xy (x+u) (y+v) := by
  ext i
  fin_cases i <;> rfl

theorem dist_xy (x y u v : ℝ) :
    dist (xy x y) (xy u v) = Real.sqrt ((x-u)^2 + (y-v)^2) := by
  simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq]

@[simp] theorem dist_xy_horiz (x u y : ℝ) : dist (xy x y) (xy u y) = |x-u| := by
  simp [dist_xy, Real.sqrt_sq_eq_abs]

@[simp] theorem dist_xy_vert (x y v : ℝ) : dist (xy x y) (xy x v) = |y-v| := by
  simp [dist_xy, Real.sqrt_sq_eq_abs]

def rectangle (a b c d : ℝ) : Finset Plane := {xy a c, xy a d, xy b c, xy b d}

theorem rectangle_nonempty (a b c d : ℝ) : (rectangle a b c d).Nonempty :=
  Finset.insert_nonempty _ _

theorem meanWidth_congr {S T : Finset Plane} (h : S = T) (hS : S.Nonempty) (hT : T.Nonempty) :
    meanWidth S hS = meanWidth T hT := by subst T; rfl

theorem meanWidth_rectangle (a b c d : ℝ) :
    meanWidth (rectangle a b c d) (rectangle_nonempty ..) = |a-b| + |c-d| := by
  let : DecidableEq Plane := Classical.decEq _
  let H : Finset Plane := {xy a 0,xy b 0}
  let V : Finset Plane := {xy 0 c,xy 0 d}
  have he : H + V = rectangle a b c d := by
    ext z
    simp only [H,V,rectangle,Finset.mem_add,Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨x, (rfl|rfl), y, (rfl|rfl), rfl⟩ <;> simp [xy_add]
    · rintro (rfl|rfl|rfl|rfl)
      · exact ⟨_,Or.inl rfl,_,Or.inl rfl, by simp [xy_add]⟩
      · exact ⟨_,Or.inl rfl,_,Or.inr rfl, by simp [xy_add]⟩
      · exact ⟨_,Or.inr rfl,_,Or.inl rfl, by simp [xy_add]⟩
      · exact ⟨_,Or.inr rfl,_,Or.inr rfl, by simp [xy_add]⟩
  have h := meanWidth_add H V (Finset.insert_nonempty _ _) (Finset.insert_nonempty _ _)
  have hH : H.Nonempty := Finset.insert_nonempty _ _
  have hV : V.Nonempty := Finset.insert_nonempty _ _
  refine (meanWidth_congr he.symm _ (hH.add hV)).trans ?_
  simpa only [H,V,meanWidth_pair,dist_xy_horiz,dist_xy_vert] using h

private theorem vertical_mem_of_convex {C : Set Plane} (hC : Convex ℝ C) {x a y b : ℝ}
    (ha : a ≤ y) (hb : y ≤ b) (h1 : xy x a ∈ C) (h2 : xy x b ∈ C) : xy x y ∈ C := by
  have hseg : y ∈ segment ℝ a b := by rw [segment_eq_Icc (ha.trans hb)]; exact ⟨ha,hb⟩
  obtain ⟨s,t,hs,ht,hst,hy⟩ := hseg
  have h := hC h1 h2 hs ht hst
  have he : s • xy x a + t • xy x b = xy x y := by
    ext i
    fin_cases i
    · change s*x+t*x = x
      rw [← add_mul,hst,one_mul]
    · exact hy
  rwa [he] at h

private theorem horizontal_mem_of_convex {C : Set Plane} (hC : Convex ℝ C) {a x b y : ℝ}
    (ha : a ≤ x) (hb : x ≤ b) (h1 : xy a y ∈ C) (h2 : xy b y ∈ C) : xy x y ∈ C := by
  have hseg : x ∈ segment ℝ a b := by rw [segment_eq_Icc (ha.trans hb)]; exact ⟨ha,hb⟩
  obtain ⟨s,t,hs,ht,hst,hx⟩ := hseg
  have h := hC h1 h2 hs ht hst
  have he : s • xy a y + t • xy b y = xy x y := by
    ext i
    fin_cases i
    · exact hx
    · change s*y+t*y = y
      rw [← add_mul,hst,one_mul]
  rwa [he] at h

theorem xy_mem_hull_vpair (x : ℝ) {a y b : ℝ} (ha : a ≤ y) (hb : y ≤ b) :
    xy x y ∈ convexHull ℝ (↑({xy x a, xy x b} : Finset Plane) : Set Plane) :=
  vertical_mem_of_convex (convex_convexHull ℝ _) ha hb
    (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))

theorem xy_mem_hull_hpair {a x b : ℝ} (y : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    xy x y ∈ convexHull ℝ (↑({xy a y, xy b y} : Finset Plane) : Set Plane) :=
  horizontal_mem_of_convex (convex_convexHull ℝ _) ha hb
    (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))

theorem xy_mem_hull_rectangle {a x b c y d : ℝ} (ha : a ≤ x) (hb : x ≤ b)
    (hc : c ≤ y) (hd : y ≤ d) :
    xy x y ∈ convexHull ℝ (rectangle a b c d : Set Plane) := by
  apply horizontal_mem_of_convex (convex_convexHull ℝ _) ha hb
  all_goals
    apply vertical_mem_of_convex (convex_convexHull ℝ _) hc hd <;>
      apply subset_convexHull ℝ _ <;> simp [rectangle]

private theorem vertical_offset_cost {y t h : ℝ} (hy : y ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hh : t ≤ |h|) :
    y + t^2/4 ≤ Real.sqrt (h^2 + y^2) := by
  apply Real.le_sqrt_of_sq_le
  have hth : t^2 ≤ h^2 := by simpa only [sq_abs] using (sq_le_sq₀ ht0 (abs_nonneg h)).2 hh
  have htt : t^2 ≤ 1 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hy),
    mul_nonneg (sq_nonneg t) (sub_nonneg.mpr htt)]

theorem meanWidth_triangle_vertical_lower {a z y t : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hz : t ≤ |a-z|) :
    1+t^2/4 ≤ meanWidth {xy a 0,xy a 1,xy z y} (Finset.insert_nonempty _ _) := by
  rw [meanWidth_triangle, dist_xy_vert, dist_xy, dist_comm (xy z y), dist_xy]
  have h₁ := vertical_offset_cost (h := a-z) (y := 1-y) (by linarith) ht0 ht1 hz
  have h₂ := vertical_offset_cost (h := a-z) hy1 ht0 ht1 hz
  simp only [zero_sub, neg_sq, abs_neg, abs_one]
  linarith

end Planar
end Sunflower
end Combinatorics
end OAI
