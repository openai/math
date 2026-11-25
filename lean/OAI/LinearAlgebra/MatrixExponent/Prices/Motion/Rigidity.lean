import Mathlib.Algebra.BigOperators.Field
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.FourArms
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.TreePrice
import OAI.LinearAlgebra.MatrixExponent.Prices.Chord
import Mathlib.Order.Filter.Cocardinal
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.Zoom

/-! # Submean tests on a valuation disk -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
open Filter
variable {F E : Type} [Field F] [Field E] {X : Type*} [PseudoMetricSpace X]

def weight {n : ℕ} (r : Option (Fin n) → ℚ) (j : Option (Fin n)) : ℝ :=
  (r j : ℝ)⁻¹ / ∑ k, (r k : ℝ)⁻¹

def MovingAt (E : Type) [Field E] [MulAction (G E) X] (A : Atlas F X) (x : X) : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] [Nonempty S]
    (a b : S → K0 E) (v : K0 E), 0 ≤ val E v →
    ∀ {n : ℕ} (c : Fin n → K0 E) (r : Option (Fin n) → ℚ),
      (∀ j, 0 ≤ val E (c j)) → (∀ i j, i ≠ j → val E (c i - c j) = 0) →
      (∀ j, 0 < r j) → (∀ i, 0 < val E (a i)) → (∀ i, 0 < val E (b i)) →
      (∀ i, 0 < val E (t (-r none) * b i)) →
      ∀ᶠ u : E in cocountable, A.Submean (weight r)
        (fun i => shift (a i + b i * v) • x)
        (fun j i => shift (a i + b i * armEnd c r (C u) j) • x)

def Moving (E : Type) [Field E] [MulAction (G E) X] (A : Atlas F X) : Prop :=
  ∀ x, MovingAt E A x

def LeafTests (A : Atlas F X) (L : K0 E → X) : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] [Nonempty S] (a b : S → K0 E) (v : K0 E),
    0 ≤ val E v → ∀ {n : ℕ} (c : Fin n → K0 E) (r : Option (Fin n) → ℚ),
      (∀ j, 0 ≤ val E (c j)) → (∀ i j, i ≠ j → val E (c i - c j) = 0) →
      (∀ j, 0 < r j) →
      ∃ u : K0 E, 0 ≤ val E u ∧ A.Submean (weight r)
        (fun i => L (a i + b i * v)) (fun j i => L (a i + b i * armEnd c r u j))

theorem cocountable_neBot (E : Type) [Uncountable E] : (cocountable (α := E)).NeBot := by
  constructor
  intro h
  have he : (∅ : Set E) ∈ cocountable := by simp [h]
  exact Set.not_countable_univ (by simpa using mem_cocountable.mp he)

theorem cocountable_countable (E : Type) : CountableInterFilter (cocountable (α := E)) :=
  cardinalInterFilter_aleph_one_iff.mp inferInstance

theorem integral_C (a : E) : 0 ≤ val E (C a) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [val_C ha]

variable {n : ℕ} {r : Option (Fin n) → ℚ}

private theorem denominator_pos (h : ∀ j, 0 < r j) : 0 < ∑ j, (r j : ℝ)⁻¹ :=
  Finset.sum_pos (fun i _ => inv_pos.mpr (Rat.cast_pos.mpr (h i))) Finset.univ_nonempty

theorem weight_pos (h : ∀ j, 0 < r j) (j) : 0 < weight r j :=
  div_pos (inv_pos.mpr (Rat.cast_pos.mpr (h j))) (denominator_pos h)

theorem weight_sum (h : ∀ j, 0 < r j) : ∑ j, weight r j = 1 := by
  unfold weight
  rw [← Finset.sum_div, div_self (denominator_pos h).ne']

theorem weight_scale (e : ℚ) (he : 0 < e) : weight (fun j => e * r j) = weight r := by
  funext j
  simp only [weight, Rat.cast_mul, mul_inv_rev, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ (inv_ne_zero (Rat.cast_ne_zero.mpr he.ne'))

theorem weight_iff (h : ∀ j, 0 < r j) (v : ℝ) (w : Option (Fin n) → ℝ) :
    v ≤ ∑ j, weight r j * w j ↔ 0 ≤ ∑ j, (w j - v) / (r j : ℝ) := by
  simp only [weight, div_mul_eq_mul_div, ← Finset.sum_div, le_div_iff₀ (denominator_pos h),
    sub_div, Finset.sum_sub_distrib, sub_nonneg]
  simp only [div_eq_mul_inv, Finset.mul_sum, mul_comm]

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end

/-!
# From leaves to points of the disk tree

The leaf metric alone does not locate midpoints in the ambient space.
A three-arm test with a moving midpoint supplies the missing estimate.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
open Routing

structure Leaves (F E X : Type) [Field F] [Field E] [PseudoMetricSpace X] where
  A : Atlas F X
  L : K0 E → X
  along : ∀ (u : Fraction) (x y : X), ∃ m, Along u x y m
  gap : ∀ x y, dist (L x) (L y) = (diskGap x y 1 1 : ℝ)
  tests : LeafTests A L

namespace Leaves
variable {F E X : Type} [Field F] [Field E] [PseudoMetricSpace X] (M : Leaves F E X)

def pt (z : K0 E) (l : ℚ) := (M.along ⟨1 / 2, by norm_num, by norm_num⟩ (M.L z) (M.L (z + t l))).choose

theorem near_leaf {x y : K0 E} {r : ℚ} (hr : r ≤ 1) (h : ↑r ≤ val E (x - y)) :
    dist (M.L x) (M.L y) ≤ 2 * (1 - (r : ℝ)) := by
  rw [M.gap]
  have hb := gap_bound hr hr hr h
  exact_mod_cast (show diskGap x y 1 1 ≤ 2 * (1 - r) by linarith)

theorem branch_leaf {x y : K0 E} {r : ℚ} (hr : r ≤ 1) (h : val E (x - y) = ↑r) :
    dist (M.L x) (M.L y) = 2 * (1 - (r : ℝ)) := by
  rw [M.gap, gap_branch hr hr h]
  push_cast
  ring

theorem ends (z : K0 E) {l : ℚ} (hl : l ≤ 1) :
    dist (M.L z) (M.L (z + t l)) = 2 * (1 - (l : ℝ)) :=
  M.branch_leaf hl (by rw [AddValuation.map_sub_swap, add_sub_cancel_left, val_t])

theorem midpoint (z : K0 E) {l : ℚ} (hl : l ≤ 1) :
    dist (M.L z) (M.pt z l) = 1 - (l : ℝ) ∧ dist (M.pt z l) (M.L (z + t l)) = 1 - (l : ℝ) := by
  have h := (M.along ⟨1 / 2, by norm_num, by norm_num⟩ (M.L z) (M.L (z + t l))).choose_spec
  have h₁ := h.start
  have h₂ := h.rev.start
  rw [dist_comm (M.L (z + t l)) _, dist_comm (M.L (z + t l)) _] at h₂
  rw [M.ends z hl] at h₁ h₂
  change dist (M.L z) (M.pt z l) = (1 / 2) * _ at h₁
  change dist (M.pt z l) (M.L (z + t l)) = (1 - 1 / 2) * _ at h₂
  constructor <;> linarith

private theorem test (z : K0 E) {l : ℚ} (hl : l ≤ 1) (b v : K0 E) (hv : 0 ≤ val E v)
    {n : ℕ} (c : Fin n → K0 E) (r : Option (Fin n) → ℚ)
    (hc : ∀ j, 0 ≤ val E (c j)) (hd : ∀ i j, i ≠ j → val E (c i - c j) = 0)
    (hr : ∀ j, 0 < r j) (p : Option (Fin n) → X)
    (hp : ∑ j, weight r j * dist (M.L z) (p j) ≤ 1 - (l : ℝ))
    (hq : ∑ j, weight r j * dist (p j) (M.L (z + t l)) ≤ 1 - (l : ℝ)) :
    ∃ u : K0 E, 0 ≤ val E u ∧
      0 ≤ ∑ j, (dist (p j) (M.L (z + b * armEnd c r u j)) - dist (M.pt z l) (M.L (z + b * v))) / (r j : ℝ) := by
  let a := ![z, z + t l, z]
  let b' := ![0, 0, b]
  obtain ⟨u, hu, h⟩ := M.tests (Fin 3) a b' v hv c r hc hd hr
  refine ⟨u, hu, (weight_iff hr _ _).mp ?_⟩
  obtain ⟨h₁, h₂⟩ := M.midpoint z hl
  have H := h.extend (fun j => (weight_pos hr j).le) (fun _ : Unit => M.pt z l)
    (fun j _ => p j) (by
      intro _
      refine ⟨0, 1, 1 / 2, ?_⟩
      simp only [a, b', Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, add_zero, h₁, h₂, M.ends z hl]
      exact ⟨by ring, by ring, hp, hq⟩)
  exact H.wire (.inr ()) (.inl 2)

private theorem outward (z : K0 E) {l a : ℚ} (hl : l ≤ 1) (ha : a ≤ l)
    (w : K0 E) (hw : 0 ≤ val E w) :
    dist (M.pt z l) (M.L (z + t a * w)) ≤ (1 - (l : ℝ)) + 2 * (1 - (a : ℝ)) := by
  refine (dist_triangle _ (M.L z) _).trans ?_
  rw [dist_comm (M.pt z l) _, (M.midpoint z hl).1, dist_comm (M.L z) _]
  exact add_le_add le_rfl (M.near_leaf (ha.trans hl) (by rw [add_sub_cancel_left]; exact scaled_le a hw))

private theorem unlimited {a b : ℝ} (h : ∀ s : ℚ, 0 < s → (s : ℝ) * a ≤ b) : a ≤ 0 := by
  by_contra! ha
  obtain ⟨s, hs⟩ := exists_rat_gt (max 0 (b / a))
  exact (h s (Rat.cast_pos.mp ((le_max_left _ _).trans_lt hs))).not_gt
    ((div_lt_iff₀ ha).mp ((le_max_right _ _).trans_lt hs))

/-- Points in the unit disk of the midpoint comparison. -/
theorem inner (z : K0 E) {l : ℚ} (hl : l ≤ 1) (v : K0 E) (hv : 0 ≤ val E v) :
    dist (M.pt z l) (M.L (z + t l * v)) ≤ 1 - (l : ℝ) := by
  rcases hl.eq_or_lt with rfl | hl
  · simpa using M.outward z le_rfl le_rfl v hv
  let h := 1 - l
  have hh : 0 < h := sub_pos.mpr hl
  have hh' : (0 : ℝ) < h := Rat.cast_pos.mpr hh
  have ee : (h : ℝ) = 1 - l := by simp [h]
  let J := dist (M.pt z l) (M.L (z + t l * v))
  have I : 2 * (J - h) ≤ 0 := by
    refine unlimited (b := (3 * (h : ℝ) - J) * h) fun s hs => ?_
    let r : Option (Fin 2) → ℚ := fun j => j.elim s (fun _ => h)
    let c : Fin 2 → K0 E := ![0, 1]
    let p : Option (Fin 2) → X := fun j => j.elim (M.pt z l) ![M.L z, M.L (z + t l)]
    have hs' : (0 : ℝ) < s := Rat.cast_pos.mpr hs
    have hr (j) : 0 < r j := by cases j <;> assumption
    have hc (j) : 0 ≤ val E (c j) := by fin_cases j <;> simp [c]
    have hd (i j) (hne : i ≠ j) : val E (c i - c j) = 0 := by
      fin_cases i <;> fin_cases j <;> simp_all [c]
    have e : weight r (some 0) = weight r (some 1) := rfl
    have sum := weight_sum hr
    rw [Fintype.sum_option, Fin.sum_univ_two, e] at sum
    have es : (weight r none + (weight r (some 1) + weight r (some 1))) * (1 - (l : ℝ)) = 1 - l := by
      rw [sum, one_mul]
    obtain ⟨u, hu, H⟩ := M.test z hl.le (t l) v hv c r hc hd hr p (by
      simp only [Fintype.sum_option, Fin.sum_univ_two, p, Option.elim_none, Option.elim_some,
        Matrix.cons_val_zero, Matrix.cons_val_one, dist_self, (M.midpoint z hl.le).1, M.ends z hl.le]
      linarith only [es]) (by
      simp only [Fintype.sum_option, Fin.sum_univ_two, p, Option.elim_none, Option.elim_some,
        Matrix.cons_val_zero, Matrix.cons_val_one, dist_self, (M.midpoint z hl.le).2, M.ends z hl.le, e]
      linarith only [es])
    simp only [Fintype.sum_option, Fin.sum_univ_two, p, c, r, armEnd, Option.elim_none, Option.elim_some,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add, mul_add, mul_one,
      ← mul_assoc, ← t_add, ← sub_eq_add_neg, show l + h = 1 by unfold h; ring] at H
    have vanish (a : K0 E) : dist (M.L a) (M.L (a + t 1 * u)) = 0 := by
      rw [dist_comm]
      apply le_antisymm _ dist_nonneg
      simpa using M.near_leaf (x := a + t 1 * u) (y := a) le_rfl
        (by rw [add_sub_cancel_left]; exact scaled_le 1 hu)
    rw [← add_assoc z (t l), vanish, vanish] at H
    have hu' := M.outward z hl.le (show l - s ≤ l by linarith) u hu
    rw [Rat.cast_sub] at hu'
    change 0 ≤ (_ - J) / _ + ((0 - J) / _ + (0 - J) / _) at H
    rw [← add_div, div_add_div _ _ hs'.ne' hh'.ne', le_div_iff₀ (mul_pos hs' hh')] at H
    rw [ee] at H ⊢
    linarith only [H, mul_le_mul_of_nonneg_right hu' (ee ▸ hh'.le)]
  linarith

/-- Any distant leaf lies on an arm through the same midpoint. -/
theorem outer (z : K0 E) {l a : ℚ} (hl : l ≤ 1) (ha : a ≤ l) (v : K0 E) (hv : 0 ≤ val E v) :
    dist (M.pt z l) (M.L (z + t a * v)) ≤ 1 + (l : ℝ) - 2 * a := by
  rcases ha.eq_or_lt with rfl | ha
  · linarith only [M.inner z hl v hv]
  let J := dist (M.pt z l) (M.L (z + t a * v))
  have e : J - (1 + (l : ℝ) - 2 * a) ≤ 0 := by
    refine unlimited (b := (3 - (l : ℝ) - 2 * a - J) * (l - a)) fun s hs => ?_
    let r : Option (Fin 1) → ℚ := fun j => j.elim s (fun _ => l - a)
    have hr : ∀ j, 0 < r j := by
      intro j; cases j
      · exact hs
      · exact sub_pos.mpr ha
    have hs' : (0 : ℝ) < s := Rat.cast_pos.mpr hs
    have ha' : (0 : ℝ) < l - a := sub_pos.mpr (Rat.cast_lt.mpr ha)
    obtain ⟨u, hu, H⟩ := M.test z hl (t a) v hv (fun _ => 0) r (by simp)
      (fun i j h => (h (Subsingleton.elim _ _)).elim) hr (fun _ => M.pt z l)
      (by simp only [← Finset.sum_mul, weight_sum hr, one_mul, (M.midpoint z hl).1, le_refl])
      (by simp only [← Finset.sum_mul, weight_sum hr, one_mul, (M.midpoint z hl).2, le_refl])
    simp only [Fintype.sum_option, Fin.sum_univ_one, r, armEnd, Option.elim_none, Option.elim_some,
      zero_add, ← mul_assoc, ← t_add, ← sub_eq_add_neg, add_sub_cancel, Rat.cast_sub] at H
    have hu' := M.outward z hl (show a - s ≤ l by linarith) u hu
    rw [Rat.cast_sub] at hu'
    change 0 ≤ (_ - J) / _ + (_ - J) / _ at H
    rw [div_add_div _ _ hs'.ne' ha'.ne', le_div_iff₀ (mul_pos hs' ha')] at H
    linarith only [H, mul_le_mul_of_nonneg_right hu' ha'.le,
      mul_le_mul_of_nonneg_left (M.inner z hl u hu) hs'.le]
  exact sub_nonpos.mp e

end Leaves
end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end

/-! # Distances between the chosen disk midpoints -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0.Leaves
open Routing
variable {F E X : Type} [Field F] [Field E] [PseudoMetricSpace X] (M : Leaves F E X)

include M in
/-- Two ordered points on a common segment have distance equal to
the difference of their distances from the initial endpoint. -/
private theorem ordered (a b x y : X)
    (hx : dist a x + dist x b = dist a b) (hy : dist a y + dist y b = dist a b)
    (hxy : dist a x ≤ dist a y) : dist x y = dist a y - dist a x := by
  refine le_antisymm ?_ (by linarith [dist_triangle a x y])
  by_cases h : dist a b = 0
  · linarith [dist_nonneg (x := x) (y := b), dist_triangle_left x y a]
  have hh : 0 < dist a b := lt_of_le_of_ne dist_nonneg (Ne.symm h)
  let s : Fraction := ⟨dist a x / dist a b, div_nonneg dist_nonneg hh.le,
    (div_le_one hh).mpr (by linarith [dist_nonneg (x := x) (y := b)])⟩
  obtain ⟨p, hp⟩ := M.along s a b
  have e : s.val * dist a b = dist a x := div_mul_cancel₀ _ h
  have bound (z : X) (hz : dist a z + dist z b = dist a b) :
      dist p z ^ 2 ≤ (dist a z - dist a x) ^ 2 := by
    refine (hp z).trans_eq ?_
    rw [dist_comm b z, show dist z b = dist a b - dist a z by linarith, ← e]
    ring
  have h₁ : dist p x = 0 := by nlinarith only [bound x hx]
  have h₂ := (sq_le_sq₀ dist_nonneg (sub_nonneg.mpr hxy)).mp (bound y hy)
  linarith [dist_triangle_left x y p]

private theorem reached {z w : K0 E} {l a : ℚ} (hl : l ≤ 1) (ha : a ≤ l)
    (h : ↑a ≤ val E (w - z)) : dist (M.pt z l) (M.L w) ≤ 1 + (l : ℝ) - 2 * a := by
  have hb := M.outer z hl ha _ (le_unscale h)
  rwa [unscale, add_sub_cancel] at hb

theorem across {z w : K0 E} {l a : ℚ} (hl : l ≤ 1) (ha : a ≤ l)
    (h : val E (w - z) = ↑a) :
    dist (M.L z) (M.pt z l) + dist (M.pt z l) (M.L w) = dist (M.L z) (M.L w) := by
  apply le_antisymm _ (dist_triangle _ _ _)
  rw [(M.midpoint z hl).1, dist_comm (M.L z) (M.L w), M.branch_leaf (ha.trans hl) h]
  linarith only [M.reached hl ha h.ge]

private theorem nested {z w : K0 E} {l m : ℚ} (hl : l ≤ m) (hm : m ≤ 1)
    (h : ↑l ≤ val E (w - z)) : dist (M.pt z l) (M.pt w m) = (m : ℝ) - l := by
  have hl' := hl.trans hm
  let u := w + t l
  have hv : val E (u - w) = ↑l := by unfold u; rw [add_sub_cancel_left, val_t]
  have hu : ↑l ≤ val E (u - z) := by
    rw [show u - z = (u - w) + (w - z) by ring]
    exact (val E).map_le_add hv.ge h
  have hx := M.reached hl' le_rfl h
  have hy := M.reached hl' le_rfl hu
  rw [dist_comm] at hx
  have hb : dist (M.L w) (M.L u) = 2 * (1 - (l : ℝ)) := M.ends w hl'
  have H := dist_triangle (M.L w) (M.pt z l) (M.L u)
  have h₁ : dist (M.L w) (M.pt z l) = 1 - (l : ℝ) := by linarith
  have h₂ := (M.midpoint w hm).1
  rw [dist_comm, M.ordered (M.L w) (M.L u) _ _ (M.across hm hl hv)
    (by linarith) (by rw [h₁, h₂]; exact sub_le_sub_left (Rat.cast_le.mpr hl) _), h₁, h₂]
  ring

private theorem separate {z w : K0 E} {l m r : ℚ} (hl : l ≤ 1) (hm : m ≤ 1)
    (hr : r ≤ l) (hr' : r ≤ m) (h : val E (z - w) = ↑r) :
    dist (M.pt z l) (M.pt w m) = (l : ℝ) + m - 2 * r := by
  have hw := M.across hm hr' h
  rw [dist_comm (M.L w) (M.L z), dist_comm (M.pt w m) (M.L z),
    dist_comm (M.L w) (M.pt w m), add_comm] at hw
  have hx := M.across hl hr ((val E).map_sub_swap w z |>.trans h)
  have h₁ := (M.midpoint z hl).1
  have h₂ := (M.midpoint w hm).1
  rw [dist_comm] at h₂
  have hd := M.branch_leaf (hr.trans hl) h
  have hr₁ : (r : ℝ) ≤ l := Rat.cast_le.mpr hr
  have hr₂ : (r : ℝ) ≤ m := Rat.cast_le.mpr hr'
  rw [M.ordered _ _ _ _ hx hw (by linarith)]
  linarith

theorem metric (z w : K0 E) {l m : ℚ} (hl : l ≤ 1) (hm : m ≤ 1) :
    dist (M.pt z l) (M.pt w m) = (diskGap z w l m : ℝ) := by
  wlog h : l ≤ m generalizing z w l m
  · rw [dist_comm, gap_symm]
    exact this w z hm hl (le_of_not_ge h)
  rcases le_or_gt (l : WithTop ℚ) (val E (z - w)) with hle | hlt
  · rw [gap_of_le h hle hl, Rat.cast_sub]
    exact M.nested h hm (by rwa [AddValuation.map_sub_swap])
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have hrl : r ≤ l := WithTop.coe_le_coe.mp (hr.trans_le hlt.le)
  rw [gap_branch hrl (hrl.trans h) hr.symm, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  exact M.separate hl hm hrl (hrl.trans h) hr.symm

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0.Leaves
end

/-!
# Submean comparison on the branches of the disk tree

For each moving leaf choose a distant endpoint whose distance
from that leaf is constant throughout the star. Harmonic depths
then give harmonic distances to both endpoints of the segment.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
variable {F E X : Type} [Field F] [Field E] [PseudoMetricSpace X]

theorem arm_bound {n : ℕ} {c : Fin n → K0 E} (hc : ∀ j, 0 ≤ val E (c j))
    {r : Option (Fin n) → ℚ} (hr : ∀ j, 0 < r j) {u : K0 E} (hu : 0 ≤ val E u)
    (j : Option (Fin n)) : ↑(-r none) ≤ val E (armEnd c r u j) := by
  cases j with
  | none => exact scaled_le _ hu
  | some j =>
    exact (WithTop.coe_le_coe.mpr (neg_nonpos.mpr (hr _).le)).trans
      ((val E).map_le_add (hc j) (scaled_pos (hr _) hu).le)

private theorem far {n : ℕ} (a b : K0 E) (s l : ℚ) (k : Option (Fin n) → ℚ) :
    ∃ (w : K0 E) (q : ℚ), q < 1 ∧ q ≤ l ∧ (∀ j, q ≤ k j) ∧
      ∀ v : K0 E, ↑(-s) ≤ val E v → val E (w - (a + b * v)) = ↑q := by
  obtain ⟨d, hd⟩ := (Set.finite_range k).bddBelow
  obtain ⟨e, he⟩ : ∃ e : ℚ, ↑e ≤ val E b := by
    cases val E b
    · exact ⟨0, le_top⟩
    · exact ⟨_, le_rfl⟩
  let q := min (min 0 (e - s - 1)) (min l d)
  have hq : q < e - s := (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt (sub_one_lt _))
  refine ⟨a + t q, q, (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt zero_lt_one),
    (min_le_right _ _).trans (min_le_left _ _),
    fun j => ((min_le_right _ _).trans (min_le_right _ _)).trans (hd ⟨j, rfl⟩), fun v hv => ?_⟩
  have hval : val E (t q) < val E (-(b * v)) := by
    rw [val_t, AddValuation.map_neg, AddValuation.map_mul]
    refine (WithTop.coe_lt_coe.mpr hq).trans_le ?_
    rw [sub_eq_add_neg, WithTop.coe_add]
    exact add_le_add he hv
  rw [show a + t q - (a + b * v) = t q + -(b * v) by ring, (val E).map_add_eq_of_lt_left hval, val_t]

private theorem average {n : ℕ} (r : Option (Fin n) → ℚ) (hr : ∀ j, 0 < r j)
    (l : ℚ) (k : Option (Fin n) → ℚ) (h : ∑ j, (k j - l) / r j = 0) :
    ∑ j, weight r j * (k j : ℝ) = (l : ℝ) := by
  have hz : ∑ j, ((k j : ℝ) - l) / r j = 0 := by
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_sub, Rat.cast_zero] using
      congrArg (fun t : ℚ => (t : ℝ)) h
  apply le_antisymm _ ((weight_iff hr _ _).mpr hz.ge)
  have ha : 0 ≤ ∑ j, (-(k j : ℝ)- -(l : ℝ)) / r j := by
    simp only [neg_sub_neg, ← neg_sub (k _ : ℝ), neg_div, Finset.sum_neg_distrib, hz, neg_zero, le_refl]
  simpa using (weight_iff hr _ _).mpr ha

theorem Leaves.harmonic (M : Leaves F E X) {n : ℕ} (a b : Four (K0 E)) (c : Fin n → K0 E)
    (hc : ∀ j, 0 ≤ val E (c j)) (hd : ∀ i j, i ≠ j → val E (c i - c j) = 0)
    (r : Option (Fin n) → ℚ) (hr : ∀ j, 0 < r j)
    (l : Four ℚ) (k : Option (Fin n) → Four ℚ)
    (hl : ∀ i, l i ≤ 1) (hk : ∀ j i, k j i ≤ 1)
    (h : ∀ i, ∑ j, (k j i - l i) / r j = 0) (v : K0 E) (hv : 0 ≤ val E v) :
    ∃ u : K0 E, 0 ≤ val E u ∧ M.A.Submean (weight r)
      (fun i => M.pt (diskAffine a b v i) (l i))
      (fun j i => M.pt (diskAffine a b (armEnd c r u j) i) (k j i)) := by
  choose w q hq hq₁ hq₂ hw using fun i => far (a i) (b i) (r none) (l i) (fun j => k j i)
  let x (t : K0 E) := Sum.elim (fun i => M.L (diskAffine a b t i)) (fun i => M.L (w i))
  let p (t : K0 E) (d : Four ℚ) (i : Fin 4) := M.pt (diskAffine a b t i) (d i)
  have H (u : K0 E) :
      (fun i => M.L (Sum.elim a w i + Sum.elim b (fun _ => 0) i * u)) = x u := by
    funext i
    cases i <;> simp [x, diskAffine]
  obtain ⟨u, hu, hh⟩ := M.tests _ (Sum.elim a w) (Sum.elim b (fun _ => 0)) v hv c r hc hd hr
  rw [H v, show (fun j i => M.L (Sum.elim a w i + Sum.elim b (fun _ => 0) i * armEnd c r u j)) =
    (fun j => x (armEnd c r u j)) from funext (fun j => H _)] at hh
  let e := armEnd c r u
  have he (i : Fin 4) (t : K0 E) (ht : ↑(-r none) ≤ val E t)
      (d : Four ℚ) (hd : d i ≤ 1) (hqd : q i ≤ d i) :
      dist (x t (.inl i)) (x t (.inr i)) = 2 * (1 - (q i : ℝ)) ∧
      dist (x t (.inl i)) (p t d i) = 1 - (d i : ℝ) ∧
      dist (p t d i) (x t (.inr i)) = (1 - 2 * (q i : ℝ)) + d i := by
    have H := hw i t ht
    change val E (w i - diskAffine a b t i) = _ at H
    have h₁ := M.branch_leaf (hq i).le H
    rw [dist_comm] at h₁
    have h₂ := (M.midpoint (diskAffine a b t i) hd).1
    have h₃ := M.across hd hqd H
    exact ⟨h₁, h₂, by dsimp [x, p]; linarith only [h₁, h₂, h₃]⟩
  have hh' := hh.extend (fun j => (weight_pos hr j).le) (p v l) (fun j => p (e j) (k j)) (by
    intro i
    obtain ⟨hi, h₁, h₂⟩ := he i v ((WithTop.coe_le_coe.mpr (neg_nonpos.mpr (hr _).le)).trans hv)
      l (hl i) (hq₁ i)
    have hj (j) := he i (e j) (arm_bound hc hr hu j) (k j) (hk j i) (hq₂ i j)
    have hd : 2 * (1 - (q i : ℝ)) ≠ 0 := by
      have ht : (q i : ℝ) < 1 := by exact_mod_cast hq i
      positivity
    let t := (1 - (l i : ℝ)) / (2 * (1 - (q i : ℝ)))
    have ht : t * (2 * (1 - (q i : ℝ))) = 1 - l i := div_mul_cancel₀ _ hd
    refine ⟨.inl i, .inr i, t, ?_, ?_, ?_, ?_⟩
    · rw [hi, h₁, ht]
    · rw [hi, h₂, sub_mul, ht]
      ring
    · change (∑ j, weight r j * dist (x (e j) (.inl i)) (p (e j) (k j) i)) ≤ _
      simp_rw [(hj _).2.1]
      rw [h₁]
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, weight_sum hr,
        average r hr _ _ (h i), le_refl]
    · change (∑ j, weight r j * dist (p (e j) (k j) i) (x (e j) (.inr i))) ≤ _
      simp_rw [(hj _).2.2]
      rw [h₂]
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, weight_sum hr, one_mul,
        average r hr _ _ (h i), le_refl])
  exact ⟨u, hu, hh'.reindex Sum.inr⟩

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end

/-!
# Submean tests on the geodesic hull

First allow a different orbit mark at every slot. Simultaneous
geodesic interpolation then gives the tests for terms. A countable
intersection and continuity in placement pass them to the closure.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices
open Spectral Filter Topology

variable {F S : Type} [Field F] [Fintype S] [DecidableEq S] [Nonempty S]
  {X : Type*} [PseudoMetricSpace X] (A : Atlas F X)

theorem Atlas.transport (T : Raw F S) (ht : Tensor.ofRaw T ≠ 0) (x y : S → X) :
    |A.price x (Tensor.ofRaw T) - A.price y (Tensor.ofRaw T)| ≤
      (∑ i, dist (x i) (y i) * Real.log (Fintype.card (T.leg i))) / Real.log 2 := by
  let _ := sum_nontrivial S S
  let z := Sum.elim x y
  obtain ⟨D, d, hd, f, hf, he⟩ := A.valid z
  have hw (i : S) : d * Tensor.dist f (.inl i) (.inr i) = dist (x i) (y i) := by
    have h := A.wire z (.inl i) (.inr i)
    rw [he] at h
    exact h
  change |A.price (z ∘ Sum.inl) _ - A.price (z ∘ Sum.inr) _| ≤ _
  rw [A.place, A.place, he]
  simp only [Function.comp_apply, Tensor.values, ← mul_sub, ← sub_div, ← mul_div_assoc,
    abs_div, abs_of_pos (Real.log_pos (show (1 : ℝ) < 2 by norm_num)), abs_mul, abs_of_nonneg hd.1]
  have h := mul_le_mul_of_nonneg_left (Tensor.price_transport f hf T ht Sum.inl Sum.inr) hd.1
  rw [Finset.mul_sum] at h
  simp only [← mul_assoc, hw] at h
  exact div_le_div_of_nonneg_right h (Real.log_nonneg (by norm_num))

theorem Atlas.continuous_price (T : Tensor F S) : Continuous (fun x : S → X => A.price x T) := by
  refine Quotient.inductionOn T fun t => ?_
  change Continuous (fun x : S → X => A.price x (Tensor.ofRaw t))
  by_cases ht : Tensor.ofRaw t = 0
  · have he (x : S → X) : A.price x 0 = 0 := by
      let _ := sum_nontrivial S S
      let z := Sum.elim x x
      obtain ⟨D, d, _, f, _, he⟩ := A.valid z
      change A.price (z ∘ Sum.inl) 0 = _
      rw [A.place, he]
      simp [Tensor.place_zero, Tensor.values]
    simp only [ht, he]
    exact continuous_const
  apply continuous_iff_continuousAt.mpr
  intro x
  let g (y : S → X) := (∑ i, dist (y i) (x i) * Real.log (Fintype.card (t.leg i))) / Real.log 2
  have hg : Continuous g := by unfold g; fun_prop
  have hzero : g x = 0 := by simp [g]
  refine tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) (g := g) ?_ ?_)
  · intro y
    rw [Real.dist_eq]
    exact A.transport t ht y x
  · rw [← hzero]
    exact hg.continuousAt

end OAI.LinearAlgebra.MatrixExponent.Prices

namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
open Filter Routing
open scoped Topology

variable {E F : Type} [Field F] [Field E] {X : Type*} [MetricSpace X]
  [MulAction (G E) X] [IsIsometricSMul (G E) X] {A : Atlas F X} {o : X}

private def depth : Term (G E) → ℕ
  | .mark _ => 0
  | .seg _ x y => max (depth x) (depth y) + 1

omit [IsIsometricSMul (G E) X] in
private theorem split_term (C : Comparison X) (o : X) {d : ℕ} (t : Term (G E)) (ht : depth t ≤ d + 1) :
    let ev := Term.eval C (fun g : G E => g • o)
    ∃ l r : Term (G E), depth l ≤ d ∧ depth r ≤ d ∧ ∃ u : ℝ,
      dist (ev l) (ev t) = u * dist (ev l) (ev r) ∧
      dist (ev t) (ev r) = (1 - u) * dist (ev l) (ev r) := by
  cases t with
  | mark g => exact ⟨.mark g, .mark g, Nat.zero_le _, Nat.zero_le _, 0, by simp, by simp⟩
  | seg u l r =>
    have h := C.along u (Term.eval C (fun g => g • o) l) (Term.eval C (fun g => g • o) r)
    refine ⟨l, r, (le_max_left _ _).trans (Nat.le_of_succ_le_succ ht),
      (le_max_right _ _).trans (Nat.le_of_succ_le_succ ht), u.val, h.start, ?_⟩
    have he := h.rev.start
    rw [dist_comm, dist_comm (Term.eval C _ r) (Term.eval C _ l)] at he
    exact he

theorem MovingAt.term (ho : MovingAt E A o) (C' : Comparison X) (T : Term (G E)) :
    MovingAt E A (T.eval C' (fun g => g • o)) := by
  intro S _ _ _ a b v hv n c r hc hd hr ha hb he
  let ev := Term.eval C' (fun g : G E => g • o)
  let m (w : K0 E) (i : S) := a i + b i * w
  let e (u : E) := armEnd c r (K0.C u)
  have mulpos {x y : K0 E} (hx : 0 < val E x) (hy : 0 ≤ val E y) : 0 < val E (x * y) := by
    rw [AddValuation.map_mul]
    exact hx.trans_le (le_add_of_nonneg_right hy)
  have hmv i : 0 < val E (m v i) := (val E).map_lt_add (ha i) (mulpos (hb i) hv)
  have hme u j i : 0 < val E (m (e u j) i) := by
    apply (val E).map_lt_add (ha i)
    cases j with
    | none =>
      rw [show e u none = t (-r none) * K0.C u from rfl, ← mul_assoc, mul_comm (b i)]
      exact mulpos (he i) (integral_C u)
    | some j =>
      apply mulpos (hb i)
      apply (val E).map_le_add (hc j)
      exact (mulpos (by rw [val_t]; exact WithTop.coe_pos.mpr (hr _)) (integral_C u)).le
  let act {U : Type} (z : U → S) (f : U → Term (G E)) (w : K0 E) (i : U) :=
    shift (m w (z i)) • ev (f i)
  have terms (d : ℕ) : ∀ (U : Type) [Fintype U] [DecidableEq U] [Nonempty U]
      (z : U → S) (f : U → Term (G E)), (∀ i, depth (f i) ≤ d) →
      ∀ᶠ u : E in cocountable, A.Submean (weight r) (act z f v) (fun j => act z f (e u j)) := by
    induction d with
    | zero =>
      intro U _ _ _ z f hf
      have marks (i : U) : ∃ g, f i = .mark g := by
        cases h : f i with
        | mark g => exact ⟨g, rfl⟩
        | seg _ _ _ => have hw := hf i; simp [h, depth] at hw
      choose g hg using marks
      let a' i := a (z i) + idx (g i)
      have hh := ho U a' (b ∘ z) v hv c r hc hd hr
        (fun i => (val E).map_lt_add (ha _) (idx_pos _)) (fun i => hb _) (fun i => he _)
      have eq (w : K0 E) (hw : ∀ i, 0 < val E (m w i)) :
          act z f w = fun i => shift (a' i + b (z i) * w) • o := by
        funext i
        unfold act
        rw [hg]
        change shift (m w (z i)) • (g i • o) = _
        rw [show a' i + b (z i) * w = m w (z i) + idx (g i) from add_right_comm _ _ _,
          shift_add (hw _) (idx_pos _), shift_idx, mul_smul]
      filter_upwards [hh] with u hu
      simp only [eq v hmv, eq _ (hme u _)]
      exact hu
    | succ d ih =>
      intro U _ _ _ z f hf
      choose l r' hl hr' t ht₁ ht₂ using fun i => split_term C' o (f i) (hf i)
      let z' := Sum.elim z z
      let f' := Sum.elim l r'
      have hf' (i : U ⊕ U) : depth (f' i) ≤ d := by cases i <;> first | exact hl _ | exact hr' _
      filter_upwards [ih (U ⊕ U) z' f' hf'] with u hu
      have hh := hu.extend (fun j => (weight_pos hr j).le) (act z f v)
        (fun j => act z f (e u j)) (fun i => by
          refine ⟨.inl i, .inr i, t i, ?_, ?_, ?_, ?_⟩
          all_goals simp only [act, z', f', Sum.elim_inl, Sum.elim_inr, dist_smul]
          · exact ht₁ i
          · exact ht₂ i
          · rw [← Finset.sum_mul, weight_sum hr, one_mul]
          · rw [← Finset.sum_mul, weight_sum hr, one_mul])
      exact hh.reindex Sum.inr
  exact terms (depth T) S id (fun _ => T) fun _ => le_rfl

theorem Moving.of_dense (ho : MovingAt E A o) (C' : Comparison X)
    (h : DenseRange (Term.eval C' (fun g : G E => g • o))) : Moving E A := by
  intro x S _ _ _ a b v hv n c r hc hd hr ha hb he
  obtain ⟨y, hy, hx⟩ := mem_closure_iff_seq_limit.mp (h x)
  let m (w : K0 E) (x : X) (i : S) := shift (a i + b i * w) • x
  let _ := cocountable_countable E
  have hw : ∀ᶠ u : E in cocountable, ∀ k : ℕ, A.Submean (weight r) (m v (y k))
      (fun j => m (armEnd c r (K0.C u) j) (y k)) := by
    apply eventually_countable_forall.mpr
    intro k
    obtain ⟨t, ht⟩ := hy k
    rw [← ht]
    exact ho.term C' t S a b v hv c r hc hd hr ha hb he
  filter_upwards [hw] with u hu
  intro B
  have hp (w : K0 E) : Continuous (fun z => A.price (m w z) B) :=
    (A.continuous_price B).comp (continuous_pi fun i => (isometry_smul X (shift (a i + b i * w))).continuous)
  have ht : IsClosed {z | A.price (m v z) B ≤
      ∑ j, weight r j * A.price (m (armEnd c r (K0.C u) j) z) B} :=
    isClosed_le (hp v) (continuous_finsetSum _ fun j _ => continuous_const.mul (hp _))
  exact ht.mem_of_tendsto hx (Eventually.of_forall fun k => hu k B)

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end

/-! # Restricting the submean comparison to a single wire -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
open Filter
variable {F E : Type} [Field F] [Field E] [Uncountable E]
    {X : Type*} [MetricSpace X] [MulAction (G E) X] {A : Atlas F X}

private theorem Moving.test (h : Moving E A) (x : X) {q : ℚ} (hq : 0 < q)
    (w : K0 E) (hw : 0 ≤ val E w) {n : ℕ} (c : Fin n → K0 E) (r : Option (Fin n) → ℚ)
    (hc : ∀ j, 0 ≤ val E (c j)) (hd : ∀ i j, i ≠ j → val E (c i - c j) = 0)
    (hr : ∀ j, 0 < r j) (hr' : r none < q) :
    ∃ u : K0 E, 0 ≤ val E u ∧
      0 ≤ ∑ j, (cost x (t q * armEnd c r u j) - cost x (t q * w)) / (r j : ℝ) := by
  have := cocountable_neBot E
  let b : Fin 2 → K0 E := ![0, t q]
  have hb : ∀ i, 0 < val E (b i) := by intro i; fin_cases i <;> simp [b, hq]
  have ht : ∀ i, 0 < val E (t (-r none) * b i) := by
    intro i
    fin_cases i
    · simp [b]
    change 0 < val E (t (-r none) * t q)
    rw [← t_add, val_t, WithTop.coe_pos]
    linarith
  obtain ⟨u, hu⟩ := (h x (Fin 2) (fun _ => 0) b w hw c r hc hd hr (by simp) hb ht).exists
  refine ⟨C u, integral_C u, (weight_iff hr _ _).mp ?_⟩
  simpa [b, cost] using hu.wire 0 1

theorem Moving.radial (h : Moving E A) : RadialStars E X := by
  constructor
  · intro x a b c ha hab hbc w hw
    let r : Option (Fin 1) → ℚ := fun j => if j = none then b - a else c - b
    have hr : ∀ j, 0 < r j := by
      intro j
      unfold r
      split <;> linarith
    obtain ⟨u, hu, h'⟩ := h.test x (ha.trans hab) w hw (fun _ => 0) r (by simp)
      (fun i j hij => (hij (Subsingleton.elim _ _)).elim) hr (by simp [r, ha])
    simp only [Fintype.sum_option, Fin.sum_univ_one, r, armEnd, zero_add, ite_true,
      Option.some_ne_none, ite_false, ← mul_assoc, ← t_add, Rat.cast_sub] at h'
    rw [show b + -(b - a) = a by ring, show b + (c - b) = c by ring] at h'
    have h₁ : (a : ℝ) < b := Rat.cast_lt.mpr hab
    have h₂ : (b : ℝ) < c := Rat.cast_lt.mpr hbc
    refine ⟨u, hu, ?_⟩
    have he : (cost x (t b * w) - cost x (t a * u)) / ((b : ℝ) - a) ≤
        (cost x (t c * u) - cost x (t b * w)) / ((c : ℝ) - b) := by
      rw [← neg_sub, neg_div]
      linarith only [h']
    rw [div_le_div_iff₀ (sub_pos.mpr h₁) (sub_pos.mpr h₂)] at he
    linarith only [he]
  · intro x q s hs hq w v hw hv
    let c : Fin 2 → K0 E := ![0, v]
    have hc (j) : 0 ≤ val E (c j) := by fin_cases j <;> simp [c, hv]
    have hd (i j) (hn : i ≠ j) : val E (c i - c j) = 0 := by
      fin_cases i <;> fin_cases j <;> simp_all [c]
    obtain ⟨u, hu, h'⟩ := h.test x (hs.trans hq) w hw c (fun _ => s) hc hd (fun _ => hs) hq
    refine ⟨u, hu, ?_⟩
    rw [← Finset.sum_div, le_div_iff₀ (Rat.cast_pos.mpr hs), zero_mul,
      Fintype.sum_option, Fin.sum_univ_two] at h'
    simp only [armEnd, c, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add, ← mul_assoc,
      ← t_add, ← sub_eq_add_neg] at h'
    linarith only [h']

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end

/-!
# Submean estimates survive the zoom

Dilation of the coefficients multiplies the lengths of all arms by
the same positive number. A single residue outside countably many
exceptions works throughout the sequence of zooms.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
open Filter Topology Routing
variable {E F : Type} [Field E] [Field F]

private theorem dilate_integral {x : K0 E} (hx : 0 ≤ val E x) {e : ℚ} (he : 0 < e) :
    0 ≤ val E (dilate e he x) := by
  rw [val_dilate]
  generalize val E x = v at *
  cases v with
  | top => simp
  | coe v =>
    rw [WithTop.map_coe, WithTop.coe_nonneg]
    exact mul_nonneg he.le (WithTop.coe_nonneg.mp hx)

private theorem Dilation.affine (D : Dilation) (i : ℕ) (a b z : K0 E) :
    D.index i (a + b * z) = D.index i a + D.index i b * dilate (D.e i) (D.pos i) z := by
  simp only [index, zoom, map_add, map_mul, mul_add, mul_assoc]

private theorem dilate_end {e : ℚ} (he : 0 < e) {n : ℕ} (c : Fin n → K0 E)
    (r : Option (Fin n) → ℚ) (u : E) (j : Option (Fin n)) :
    dilate e he (armEnd c r (C u) j) =
      armEnd (dilate e he ∘ c) (fun k => e * r k) (C u) j := by
  cases j <;> simp [armEnd]

variable {X : Type} [MetricSpace X] [MulAction (G E) X] {A : Atlas F X}

private theorem Moving.zoom [Uncountable E] (h : Moving E A) (D : Dilation) (x : X)
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (a b : S → K0 E) (v : K0 E) (hv : 0 ≤ val E v)
    {n : ℕ} (c : Fin n → K0 E) (r : Option (Fin n) → ℚ)
    (hc : ∀ j, 0 ≤ val E (c j)) (hd : ∀ i j, i ≠ j → val E (c i - c j) = 0)
    (hr : ∀ j, 0 < r j) :
    ∃ u : E, ∀ᶠ i in atTop, A.Submean (weight r)
      (fun j => D.point x i (a j + b j * v))
      (fun k j => D.point x i (a j + b j * armEnd c r (C u) k)) := by
  let event (i : ℕ) := ∀ j, 0 < val E (D.index i (a j)) ∧ 0 < val E (D.index i (b j)) ∧
      0 < val E (D.index i (t (-r none) * b j))
  have he : ∀ᶠ i in atTop, event i := eventually_all.mpr fun j =>
    (D.positive _).and ((D.positive _).and (D.positive _))
  have := cocountable_neBot E
  have := cocountable_countable E
  have aux : ∀ᶠ u : E in cocountable, ∀ i, event i → A.Submean (weight r)
      (fun j => D.point x i (a j + b j * v))
      (fun k j => D.point x i (a j + b j * armEnd c r (C u) k)) := by
    refine eventually_countable_forall.mpr fun i => ?_
    by_cases hi : event i
    swap
    · exact Eventually.of_forall (fun _ h => (hi h).elim)
    let f := dilate (E := E) (D.e i) (D.pos i)
    let t' (k) := D.e i * r k
    have hd' (j k) (hj : j ≠ k) : val E ((f ∘ c) j - (f ∘ c) k) = 0 := by
      rw [Function.comp_apply, Function.comp_apply, ← map_sub, val_dilate, hd j k hj]
      simp
    have hb' (j) : 0 < val E (t (-t' none) * D.index i (b j)) := by
      have heq : D.index i (t (-r none) * b j) = t (-t' none) * D.index i (b j) := by
        simp only [Dilation.index, K0.zoom, map_mul, dilate_t, mul_neg, t']
        rw [mul_left_comm]
      rw [← heq]
      exact (hi j).2.2
    have H := h x S (fun j => D.index i (a j)) (fun j => D.index i (b j)) (f v)
      (dilate_integral hv _) (f ∘ c) t' (fun j => dilate_integral (hc j) _) hd'
      (fun j => mul_pos (D.pos i) (hr j)) (fun j => (hi j).1) (fun j => (hi j).2.1) hb'
    filter_upwards [H] with u hu _
    rw [show weight t' = weight r from weight_scale _ (D.pos i)] at hu
    simpa only [Dilation.point, Dilation.affine, dilate_end] using hu
  obtain ⟨u, hu⟩ := aux.exists
  exact ⟨u, he.mono hu⟩

theorem Moving.limit [Uncountable E] [CompleteSpace X] [IsIsometricSMul (G E) X]
    (h : Moving E A) (C : Comparison X) {M : ℝ} (hM : ∀ x y : X, dist x y ≤ M)
    (o : X) (hm : ∃ a : ℝ, 0 < a ∧ o ∉ fixed (level E a))
    (hs : ∀ ε : ℝ, 0 < ε → ∃ b, 0 < b ∧ profile E o b < ε) :
    ∃ (Y : Type) (_ : PseudoMetricSpace Y) (B : Atlas F Y) (L : K0 E → Y),
      (∀ (u : Fraction) (x y : Y), ∃ m, Along u x y m) ∧
      (∀ x y, dist (L x) (L y) = (diskDist (leaf x) (leaf y) : ℝ)) ∧ LeafTests B L := by
  obtain ⟨x, D, _, hw⟩ := h.radial.leaves C hM o hm hs
  let R : Rescale ℕ :=
    { Y := fun _ => X, o := fun _ => x, d := D.factor
      hn := fun i => (D.pos_factor i).le, l := Ultrafilter.of atTop }
  have hl : (R.l : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  let L (z : K0 E) : R.Site := ⟨fun i => D.point x i z, by
    have hd := (hw z 0).eventually_le_const (lt_add_one _)
    refine ⟨(diskDist (leaf z) (leaf 0) : ℝ) + 1, hl ?_⟩
    have he (i : ℕ) : D.point x i (0 : K0 E) = x := by simp [Dilation.point, Dilation.index, K0.zoom]
    simp only [he] at hd
    exact hd⟩
  obtain ⟨B, hB⟩ := R.atlas (fun _ => A)
  refine ⟨R.Site, inferInstance, B, L, fun t x y => ⟨_, R.along (fun _ => C) t x y⟩,
    fun z w => tendsto_nhds_unique (R.distance (L z) (L w)) ((hw z w).mono_left hl), ?_⟩
  intro S _ _ _ a b v hv n c r hc hd hr
  obtain ⟨u, hu⟩ := h.zoom D x a b v hv c r hc hd hr
  refine ⟨K0.C u, integral_C u, fun Z => ?_⟩
  apply le_of_tendsto_of_tendsto (hB _ Z)
    (tendsto_finsetSum _ (fun j _ => (hB _ Z).const_mul (weight r j)))
  filter_upwards [hl hu] with i hi
  have hy := mul_le_mul_of_nonneg_left (hi Z) (D.pos_factor i).le
  rw [Finset.mul_sum] at hy
  exact hy.trans_eq (Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _)

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end

/-!
# Rigidity of analytic motion

A nonconstant action with the disk tests and continuity at the origin
produces a configuration of leaves on the disk tree. Excluding
that configuration forces the action to fix the chosen mark.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
variable {F E X : Type} [Field F] [Field E]

def Leaves.tree [PseudoMetricSpace X] (M : Leaves F E X) : MotionTree F E where
  rate x l := M.A.price (fun i => M.pt (x i) (l i)) 2
  realized x l hl := by
    let p := fun i => M.pt (x i) (l i)
    obtain ⟨D, hD⟩ := M.A.valid p
    exact ⟨D, _, hD, rfl, fun i j => (M.A.wire p i j).trans (M.metric _ _ (hl i) (hl j))⟩
  chord x y z l m k hl hm hk θ h₀ h₁ left right := by
    refine M.A.chord (Rat.cast_nonneg.mpr h₀) (by exact_mod_cast h₁) ?_ ?_ 2
    · intro i
      rw [M.metric _ _ (hl i) (hk i), M.metric _ _ (hl i) (hm i), left i, Rat.cast_mul]
    · intro i
      rw [M.metric _ _ (hk i) (hm i), M.metric _ _ (hl i) (hm i), right i,
        Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
  star a b c hc hd r hr l k hl hk he v hv := by
    obtain ⟨u, hu, H⟩ := M.harmonic a b c hc hd r hr l k hl hk he v hv
    exact ⟨fun _ => u, fun _ => hu, (weight_iff hr _ _).mp (H 2)⟩

variable [Uncountable E] [MetricSpace X] [CompleteSpace X]
  [MulAction (G E) X] [IsIsometricSMul (G E) X] {A : Atlas F X}

/-- Continuity need only hold at the chosen mark. -/
theorem Moving.constant (h : Moving E A) (C : Routing.Comparison X) {M : ℝ}
    (hM : ∀ x y : X, dist x y ≤ M) (o : X)
    (hs : ∀ ε : ℝ, 0 < ε → ∃ b, 0 < b ∧ profile E o b < ε)
    (hF : ∀ (Y : Type) [PseudoMetricSpace Y], Leaves F E Y → False) : ∀ g : G E, g • o = o := by
  intro g
  by_contra hn
  have hz : idx g ≠ 0 := by
    intro he
    apply hn
    rw [← shift_idx g, he, shift_zero, one_smul]
  obtain ⟨s, hv⟩ := WithTop.ne_top_iff_exists.mp ((val E).ne_top_iff.mpr hz)
  have hpos : 0 < s := WithTop.coe_pos.mp (hv.symm ▸ idx_pos g)
  have moved : o ∉ fixed (level E s) := fun hy => hn (hy g ((mem_level _ _).mpr hv.le))
  obtain ⟨Y, _, B, L, ha, hw, ht⟩ := h.limit C hM o ⟨s, Rat.cast_pos.mpr hpos, moved⟩ hs
  exact hF Y ⟨B, L, ha, hw, ht⟩

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end
