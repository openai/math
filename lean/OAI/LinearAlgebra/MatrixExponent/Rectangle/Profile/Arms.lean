import OAI.LinearAlgebra.MatrixExponent.Rectangle.Face.Contact
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Scale
import OAI.LinearAlgebra.MatrixExponent.Prices.Chord

/-! # Critical widths for a tripod with positive arms -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Minimum

def mass (v : Vec) := ∑ i, v i

def criticalWidth (v : Vec) (i : Fin 3) := 1 - v i / mass v

def opposite (v : Vec) (i : Fin 3) := mass v⁻¹ - (v i)⁻¹

def residual (D : Vec → ℝ) (v : Vec) (i : Fin 3) := D v⁻¹ - opposite v i

variable {v : Vec} {i j k : Fin 3}

theorem mass_pos (hv : Positive v) : 0 < mass v :=
  Finset.sum_pos (fun i _ => hv i) Finset.univ_nonempty

theorem mass_eq (v : Vec) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    mass v = v i + v j + v k := by
  have he : {i, j, k} = (Finset.univ : Finset (Fin 3)) := by
    apply Finset.eq_univ_of_card
    simp [hij, hik, hjk]
  simp [mass, ← he, hij, hik, hjk, add_assoc]

theorem critical_pos (hv : Positive v) : Positive (criticalWidth v) := by
  intro i
  apply sub_pos.mpr
  apply (div_lt_one (mass_pos hv)).mpr
  rw [mass_eq v (i := i) (j := i + 1) (k := i + 2) (by omega) (by omega) (by omega)]
  linarith [hv (i + 1), hv (i + 2)]

theorem critical_le (hv : Positive v) (i : Fin 3) : criticalWidth v i ≤ 1 :=
  sub_le_self _ (div_nonneg (hv i).le (mass_pos hv).le)

theorem critical_sum (hv : Positive v) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    criticalWidth v i + criticalWidth v j + criticalWidth v k = 2 := by
  have hm := (mass_pos hv).ne'
  unfold criticalWidth
  field_simp
  rw [mass_eq v hij hik hjk]
  ring

theorem opposite_eq (v : Vec) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    opposite v i = (v j)⁻¹ + (v k)⁻¹ := by
  rw [opposite, mass_eq v⁻¹ hij hik hjk]
  simp only [Pi.inv_apply]
  ring

theorem opposite_pos (hv : Positive v) : Positive (opposite v) := by
  intro i
  rw [opposite_eq v (i := i) (j := i + 1) (k := i + 2) (by omega) (by omega) (by omega)]
  exact add_pos (inv_pos.mpr (hv _)) (inv_pos.mpr (hv _))

theorem critical_pair (D : Vec → ℝ) (hv : Positive v) (hij : i ≠ j) :
    D v⁻¹ = opposite v i * criticalWidth v j + opposite v j * criticalWidth v i + defect D v := by
  obtain ⟨k, hik, hjk⟩ := other hij
  have hi := hv i
  have hj := hv j
  have hk := hv k
  change _ = _ + (D v⁻¹ - mass v⁻¹ + (mass v)⁻¹)
  unfold opposite criticalWidth
  rw [mass_eq v hij hik hjk, mass_eq v⁻¹ hij hik hjk]
  simp only [Pi.inv_apply]
  field_simp
  ring

theorem residual_eq (D : Vec → ℝ) (hv : Positive v) (i : Fin 3) :
    residual D v i = (v i)⁻¹ * criticalWidth v i + defect D v := by
  unfold residual opposite criticalWidth
  change _ = _ + (D v⁻¹ - mass v⁻¹ + (mass v)⁻¹)
  have hi := hv i
  have hm := mass_pos hv
  field_simp
  ring

theorem residual_bounds {F : Type} [Field F] {D : Vec → ℝ} (h : StarTripod F D)
    (hv : Positive v) (i : Fin 3) : 0 < residual D v i ∧ residual D v i ≤ (v i)⁻¹ := by
  constructor
  · rw [residual_eq D hv i]
    exact add_pos_of_pos_of_nonneg (mul_pos (inv_pos.mpr (hv i)) (critical_pos hv i))
      (h.toTripod.regular.nonneg _ hv)
  · have he := h.star v⁻¹ (fun i => inv_pos.mpr (hv i))
    unfold residual opposite mass
    linarith

/-- Widths stay bounded below locally even towards a reciprocal face. -/
theorem uniform_width (hv : Positive v) : ∃ ε : ℝ, 0 < ε ∧ ∀ w, Positive w →
    w ≤ (2 : ℝ) • v → v 1 ≤ w 1 → v 2 ≤ w 2 → ∀ i, ε ≤ criticalWidth w i := by
  let m := min (v 1) (v 2)
  have hm : 0 < m := lt_min (hv 1) (hv 2)
  have hv' := mass_pos hv
  refine ⟨m / (2 * mass v), by positivity, ?_⟩
  intro w hw hbound h₁ h₂ i
  have hw' := mass_pos hw
  have ht : mass w ≤ 2 * mass v := by
    unfold mass
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hbound i
  have hi : m ≤ mass w - w i := by
    rw [mass, Fin.sum_univ_three]
    have h₁' : m ≤ w 1 := (min_le_left _ _).trans h₁
    have h₂' : m ≤ w 2 := (min_le_right _ _).trans h₂
    fin_cases i <;> simp <;> linarith [hw 0, hw 1, hw 2]
  calc
    _ ≤ m / mass w := div_le_div_of_nonneg_left hm.le hw' ht
    _ ≤ (mass w - w i) / mass w := div_le_div_of_nonneg_right hi hw'.le
    _ = criticalWidth w i := by rw [sub_div, div_self hw'.ne']; rfl

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-! A tripod of three rays with a common origin. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

structure Twig where
  arm : Fin 3
  length : ℝ

namespace Twig
open Minimum Spectral

def radius (x : Twig) := max x.length 0

theorem radius_nonneg (x : Twig) : 0 ≤ x.radius := le_max_right _ _

def gap (x y : Twig) : ℝ :=
  if x.arm = y.arm then |x.radius - y.radius| else x.radius + y.radius

instance : PseudoMetricSpace Twig where
  dist := gap
  dist_self x := by simp [gap]
  dist_comm x y := by simp [gap, eq_comm, abs_sub_comm, add_comm]
  dist_triangle x y z := by
    have hx := x.radius_nonneg
    have hy := y.radius_nonneg
    have hz := z.radius_nonneg
    unfold gap
    grind [abs_sub_le, abs_sub_comm]

theorem dist_eq (x y : Twig) : Dist.dist x y =
    if x.arm = y.arm then |x.radius - y.radius| else x.radius + y.radius := rfl

def mark (a : Vec) (i : Fin 3) : Twig := ⟨i, a i⟩
def origin : Twig := ⟨0, 0⟩
def dilate (s : ℝ) (x : Twig) : Twig := ⟨x.arm, s * x.length⟩

theorem radius_dilate (s : ℝ) (hs : 0 ≤ s) (x : Twig) : (dilate s x).radius = s * x.radius := by
  simp [radius, dilate, mul_max_of_nonneg _ _ hs]

theorem dilate_dist (s : ℝ) (hs : 0 ≤ s) (x y : Twig) :
    Dist.dist (dilate s x) (dilate s y) = s * Dist.dist x y := by
  simp only [dist_eq, radius_dilate _ hs, mul_ite, ← mul_sub, abs_mul, abs_of_nonneg hs, ← mul_add]
  rfl

@[simp] theorem origin_dist (x : Twig) : Dist.dist origin x = x.radius := by
  rw [dist_eq]
  simp only [show origin.radius = 0 by simp [origin, radius], zero_sub, zero_add, abs_neg,
    abs_of_nonneg x.radius_nonneg, ite_self]

theorem radial_dist (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (x : Twig) :
    Dist.dist (dilate s x) (dilate t x) = |s - t| * x.radius := by
  rw [dist_eq, ite_eq_left (by rfl), radius_dilate s hs, radius_dilate t ht, ← sub_mul,
    abs_mul, abs_of_nonneg x.radius_nonneg]

theorem mark_dist {x y : Vec} (hx : Positive x) (hy : Positive y) (i j : Fin 3) :
    Dist.dist (mark x i) (mark y j) = if i = j then |x i - y j| else x i + y j := by
  simp [dist_eq, mark, radius, (hx i).le, (hy j).le]

variable {F : Type} [Field F]

def label (A : MatrixExponent.Prices.Atlas F Twig) (x : Vec) := A.price (mark x) 2

def Homogeneous (A : MatrixExponent.Prices.Atlas F Twig) : Prop :=
  ∀ {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (v : S → Twig) (s : ℝ), 0 < s →
    ∀ T, A.price (dilate s ∘ v) T = s * A.price v T

end Twig
end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-! A homogeneous atlas on three rays supplies a spectral tripod. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Spectral Minimum
open scoped NNReal

variable {F : Type} [Field F]

/-- Normalize an ordinary three-terminal placement with at least one
nonzero edge to a spectral point. -/
theorem prices_of_ordinary {P : Tensor F (Fin 3) → ℝ} {D x y z : ℝ}
    (h : P ∈ Tensor.ordinary F (Fin 3) D) (hxy : P (Tensor.wire F 0 1 2) = x + y)
    (hxz : P (Tensor.wire F 0 2 2) = x + z) (hyz : P (Tensor.wire F 1 2 2) = y + z)
    (hn : 0 < y + z) : 0 < P 2 ∧ Prices F (x / P 2) (y / P 2) (z / P 2) := by
  obtain ⟨d, hd, f, hf, rfl⟩ := h
  have he : Tensor.values d f 2 = d := by
    rw [Tensor.values, map_ofNat, div_self (Real.log_pos (by norm_num)).ne', mul_one]
  have hp : 0 < d := hd.1.lt_of_ne (by intro h; simp [← h, Tensor.values] at hyz; linarith)
  have h₀ (A : Tensor F (Fin 3)) : 0 ≤ f A := by simpa using hf (Tensor.zero_le A)
  let v : Point F :=
    { toFun := fun A => ⟨f A, h₀ A⟩
      map_zero' := Subtype.ext f.map_zero
      map_one' := Subtype.ext f.map_one
      map_add' := fun A B => Subtype.ext (f.map_add A B)
      map_mul' := fun A B => Subtype.ext (f.map_mul A B) }
  have hdist (i j : Fin 3) (a b : ℝ) (h : Tensor.values d f (Tensor.wire F i j 2) = a + b) :
      dist v i j = a / d + b / d := by
    rw [← add_div, eq_div_iff hp.ne', mul_comm]
    exact h
  rw [he]
  exact ⟨hp, v, fun i j h => hf h, hdist _ _ _ _ hxy, hdist _ _ _ _ hxz, hdist _ _ _ _ hyz⟩

namespace Twig

variable (A : MatrixExponent.Prices.Atlas F Twig) {a : Vec}

private theorem positive_update (ha : Positive a) (i : Fin 3) {r : ℝ} (hr : 0 < r) :
    Positive (Function.update a i r) := by
  intro j
  by_cases h : j = i <;> simp [h, hr, ha j]

private theorem update_dist (ha : Positive a) (i j : Fin 3) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    Dist.dist (mark (Function.update a i x) j) (mark (Function.update a i y) j) =
      if j = i then |x - y| else 0 := by
  rw [mark_dist (positive_update ha i hx) (positive_update ha i hy)]
  by_cases h : j = i <;> simp [h]

theorem label_convex (ha : Positive a) (i : Fin 3) :
    ConvexOn ℝ (Set.Ioi 0) (fun t => label A (Function.update a i t)) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy u v hu hv h
  have he : u = 1 - v := by linarith
  let z := u * x + v * y
  have hz : 0 < z := convex_Ioi (0 : ℝ) hx hy hu hv h
  let f t := mark (Function.update a i t)
  have hh (j : Fin 3) : Dist.dist (f x j) (f z j) = v * Dist.dist (f x j) (f y j) := by
    unfold f
    rw [update_dist ha _ _ hx hz, update_dist ha _ _ hx hy]
    rw [show x - z = v * (x - y) by unfold z; rw [he]; ring, abs_mul, abs_of_nonneg hv, mul_ite, mul_zero]
  have hk (j : Fin 3) : Dist.dist (f z j) (f y j) = (1 - v) * Dist.dist (f x j) (f y j) := by
    unfold f
    rw [update_dist ha _ _ hz hy, update_dist ha _ _ hx hy]
    rw [show z - y = u * (x - y) by unfold z; rw [he]; ring, abs_mul, abs_of_nonneg hu, ← he, mul_ite, mul_zero]
  change A.price (f z) 2 ≤ u * A.price (f x) 2 + v * A.price (f y) 2
  rw [he]
  exact A.chord hv (by linarith) hh hk _

theorem Homogeneous.star {A : MatrixExponent.Prices.Atlas F Twig} (h : Homogeneous A) :
    StarTripod F (label A) := by
  have hp (a : Vec) (ha : Positive a) :
      0 < label A a ∧ Prices F (a 0 / label A a) (a 1 / label A a) (a 2 / label A a) := by
    obtain ⟨D, hD⟩ := A.valid (mark a)
    apply prices_of_ordinary hD
    · simp [A.wire, mark_dist ha ha]
    · simp [A.wire, mark_dist ha ha]
    · simp [A.wire, mark_dist ha ha]
    · exact add_pos (ha 1) (ha 2)
  refine ⟨⟨fun a ha => (hp a ha).1, fun a ha => (hp a ha).2, fun a _ s hs => h (mark a) s hs _,
    fun _ ha i => label_convex A ha i, ?_⟩, ?_⟩
  · intro a ha i x hx y hy hxy
    have hm := A.label_move (mark (Function.update a i x)) (mark (Function.update a i y))
    simp only [update_dist ha i _ hx hy, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      abs_of_nonpos (sub_nonpos.mpr hxy)] at hm
    unfold label
    linarith only [(abs_le.mp hm).2]
  · intro a ha
    have hm := A.label_move (fun _ : Fin 3 => origin) (mark a)
    rw [A.collapsed _ (by simp) 2, zero_sub, abs_neg] at hm
    have he i : Dist.dist origin (mark a i) = a i := by simp [mark, radius, (ha i).le]
    simp only [he] at hm
    exact (le_abs_self _).trans hm

end Twig
end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-!
# The homogeneous tangent

Dilation along the rays decreases each normalized price as the radius
tends to zero. At the origin the tangent prices are their infima.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Twig

open Spectral Filter
open scoped Topology

variable {F S : Type} [Field F] [Fintype S] [DecidableEq S] [Nonempty S]

theorem dilate_mul (t s : ℝ) (x : Twig) : dilate t (dilate s x) = dilate (t * s) x := by
  simp [dilate, mul_assoc]

variable (A : MatrixExponent.Prices.Atlas F Twig) (v : S → Twig) (T : Tensor F S)

private def slope (r : ℝ) := A.price (dilate r ∘ v) T / r

private theorem slope_mono : MonotoneOn (slope A v T) (Set.Ioi 0) := by
  intro a ha b hb h
  change 0 < a at ha
  change 0 < b at hb
  have h₁ (i : S) : Dist.dist origin (dilate a (v i)) = a / b * Dist.dist origin (dilate b (v i)) := by
    rw [origin_dist, origin_dist, radius_dilate _ ha.le, radius_dilate _ hb.le, ← mul_assoc,
      div_mul_cancel₀ _ hb.ne']
  have h₂ (i : S) : Dist.dist (dilate a (v i)) (dilate b (v i)) =
      (1 - a / b) * Dist.dist origin (dilate b (v i)) := by
    rw [origin_dist, radius_dilate _ hb.le, radial_dist _ _ ha.le hb.le, abs_of_nonpos (sub_nonpos.mpr h),
      ← mul_assoc, sub_mul, one_mul, div_mul_cancel₀ _ hb.ne', neg_sub]
  have hc := A.chord (x := fun _ => origin) (y := dilate b ∘ v) (z := dilate a ∘ v)
    (div_nonneg ha.le hb.le) ((div_le_one hb).mpr h) h₁ h₂ T
  rw [A.collapsed (fun _ : S => origin) (by simp) T, mul_zero, zero_add] at hc
  rw [slope, slope, div_le_iff₀ ha]
  refine hc.trans_eq ?_
  ring

private theorem slope_rescale {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    slope A (dilate s ∘ v) T t = s * slope A v T (t * s) := by
  have eq : dilate t ∘ (dilate s ∘ v) = dilate (t * s) ∘ v := funext fun i => dilate_mul _ _ _
  rw [slope, slope, eq]
  field_simp

private def mag (n : ℕ) : ℝ := n + 1

private theorem mag_pos (n : ℕ) : 0 < mag n := by unfold mag; positivity

private theorem inv_mag_limit : Tendsto (fun n => (mag n)⁻¹) atTop (𝓝 0) := by
  simpa [mag] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem tangent : ∃ B : MatrixExponent.Prices.Atlas F Twig, Homogeneous B ∧
    ∀ {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (v : S → Twig) (T : Tensor F S),
      B.price v T ≤ A.price v T := by
  let l := Ultrafilter.of (atTop : Filter ℕ)
  have hl : (l : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨B, hB⟩ := MatrixExponent.Prices.Atlas.scaled_limit l (fun _ => Twig) (fun _ => A)
    (fun n => dilate (mag n)⁻¹) mag (fun n => (mag_pos n).le) (fun x y => by
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
      dsimp only
      rw [dilate_dist _ (inv_nonneg.mpr (mag_pos n).le), ← mul_assoc, mul_inv_cancel₀ (mag_pos n).ne',
        one_mul])
  have lim {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (v : S → Twig) (T : Tensor F S) :
      Tendsto (fun n => slope A v T (mag n)⁻¹) (l : Filter ℕ) (𝓝 (B.price v T)) := by
    refine (hB v T).congr' (Eventually.of_forall fun n => ?_)
    dsimp only
    rw [slope, div_inv_eq_mul, mul_comm]
    rfl
  have below {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (v : S → Twig) (T : Tensor F S)
      (r : ℝ) (hr : 0 < r) : B.price v T ≤ slope A v T r := by
    apply le_of_tendsto (lim v T)
    filter_upwards [(inv_mag_limit.mono_left hl).eventually_le_const hr] with n hn
    exact slope_mono A v T (inv_pos.mpr (mag_pos n)) hr hn
  have above {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (v : S → Twig) (T : Tensor F S)
      (a : ℝ) (ha : ∀ r, 0 < r → a ≤ slope A v T r) : a ≤ B.price v T :=
    ge_of_tendsto (lim v T) (Eventually.of_forall fun n => ha _ (inv_pos.mpr (mag_pos n)))
  refine ⟨B, ?_, ?_⟩
  · intro S _ _ _ v s hs T
    refine le_antisymm ?_ ?_
    · rw [mul_comm, ← div_le_iff₀ hs]
      refine above v T _ fun r hr => ?_
      rw [div_le_iff₀ hs, mul_comm]
      have h := below (dilate s ∘ v) T (r / s) (div_pos hr hs)
      rwa [slope_rescale _ _ _ (div_pos hr hs) hs, div_mul_cancel₀ _ hs.ne'] at h
    · refine above _ _ _ fun t ht => ?_
      rw [slope_rescale _ _ _ ht hs]
      exact mul_le_mul_of_nonneg_left (below _ _ _ (mul_pos ht hs)) hs.le
  · intro S _ _ _ v T
    have he : dilate 1 ∘ v = v := by funext i; simp [dilate]
    simpa [slope, he] using below v T 1 zero_lt_one

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Twig
end
