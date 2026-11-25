import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.ScaleSlope
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryTerms
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.TreePrice

/-!
# First displacement in a decreasing filtration of isometric actions

Orbit centers bound the change in distance to the fixed set.
The unique nearest fixed point inherits all symmetries of that set
fixing the original mark.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion
open Routing Set
variable {X G : Type*} [MetricSpace X] [Group G] [MulAction G X]

def displacement (H : Subgroup G) (x : X) : ℝ := ⨆ g : H, dist x ((g : G) • x)

def fixed (H : Subgroup G) : Set X := {x | ∀ g ∈ H, g • x = x}

variable {H : Subgroup G} {x : X}

theorem displacement_le {r : ℝ} (h : ∀ g ∈ H, dist x (g • x) ≤ r) :
    displacement H x ≤ r := ciSup_le fun g => h g g.property

theorem le_displacement {M : ℝ} (h : ∀ g ∈ H, dist x (g • x) ≤ M) {g : G} (hg : g ∈ H) :
    dist x (g • x) ≤ displacement H x := by
  have hb : BddAbove (range fun g : H => dist x ((g : G) • x)) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact h i i.property
  exact le_ciSup hb ⟨g, hg⟩

theorem displacement_eq {g : G} (hg : g ∈ H) (h : ∀ a ∈ H, dist x (a • x) ≤ dist x (g • x)) :
    displacement H x = dist x (g • x) :=
  le_antisymm (displacement_le h) (le_displacement h hg)

theorem displacement_fixed (h : x ∈ fixed H) : displacement H x = 0 := by
  unfold displacement
  have hz (g : H) : dist x ((g : G) • x) = 0 := by rw [h _ g.property, dist_self]
  simp only [hz, ciSup_const]

variable [CompleteSpace X] [IsIsometricSMul G X] (C : Comparison X)

private theorem nearby (C : Comparison X) {M : ℝ} (h : ∀ g ∈ H, dist x (g • x) ≤ M) :
    ∃ y ∈ fixed H, dist x y ≤ displacement H x := by
  have h₀ := dist_nonneg.trans (le_displacement h H.one_mem)
  obtain ⟨y, hy, hd⟩ := C.orbit H x (displacement H x ^ 2)
    (fun _ hg => pow_le_pow_left₀ dist_nonneg (le_displacement h hg) 2)
  exact ⟨y, hy, (sq_le_sq₀ dist_nonneg h₀).mp (by linarith [sq_nonneg (dist x y)])⟩

private theorem project (C : Comparison X) (H : Subgroup G)
    (x : X) (hn : (fixed H : Set X).Nonempty) :
    ∃ y ∈ fixed H, ∀ z ∈ fixed H, dist x y ^ 2 + dist y z ^ 2 ≤ dist x z ^ 2 := by
  have closed : IsClosed (fixed H : Set X) := by
    unfold fixed
    simp only [ofPred_forall]
    exact isClosed_iInter fun g => isClosed_iInter fun _ => isClosed_eq
      (isometry_smul X g).continuous continuous_id
  let Y := ↥(fixed H : Set X)
  have : CompleteSpace Y := closed.completeSpace_coe
  let F (_ : Unit) (z : Y) := dist x z.val ^ 2
  obtain ⟨z, hz⟩ := hn
  obtain ⟨o, a, ha, ho⟩ := Routing.minimize F (fun _ => by unfold F; fun_prop)
    (fun _ _ => sq_nonneg _) ⟨dist x z ^ 2, ⟨z, hz⟩, fun _ => le_rfl⟩ (by
      intro p q t ht hu
      let u : Fraction := ⟨t, ht, hu⟩
      let m := C.seg u p.val q.val
      have hm := C.along u p.val q.val
      have stable : m ∈ fixed H := by
        intro g hg
        apply Along.unique _ hm
        intro v
        have hd (a b : X) : dist a (g⁻¹ • b) = dist (g • a) b := by
          rw [← dist_smul g, smul_inv_smul]
        simpa only [hd, p.property g hg, q.property g hg] using hm (g⁻¹ • v)
      refine ⟨⟨m, stable⟩, fun _ => ?_⟩
      change dist x m ^ 2 ≤ (1 - t) * dist x p.val ^ 2 + t * dist x q.val ^ 2 -
        t * (1 - t) * dist p.val q.val ^ 2
      simpa only [dist_comm _ x] using hm x)
  exact ⟨o.val, o.property, fun y hy =>
    (add_le_add_left (ha ()) _).trans (ho ⟨y, hy⟩ (dist x y ^ 2) fun _ => le_rfl)⟩

/-- The center at the critical radius is fixed by every symmetry fixing
the base mark and mapping the fixed set into itself. -/
theorem motion_scale (C : Comparison X) (H : ℝ → Subgroup G)
    (hm : AntitoneOn H (Ioi 0)) {M : ℝ} (hM : ∀ x y : X, dist x y ≤ M)
    (hs : ∀ x : X, RationalSecants (fun r => displacement (H r) x))
    (o : X) (hmoved : ∃ a : ℝ, 0 < a ∧ o ∉ fixed (H a))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ b, 0 < b ∧ displacement (H b) o < ε) :
    ∃ (r : ℝ) (A : X) (k : ℝ), 0 < r ∧ 0 < k ∧ A ∈ fixed (H r) ∧
      (∀ φ : X → X, Isometry φ → φ o = o → MapsTo φ (fixed (H r)) (fixed (H r)) → φ A = A) ∧
      Kink (fun s => displacement (H s) A) r k := by
  have bound (x : X) (r : ℝ) : ∀ g ∈ H r, dist x (g • x) ≤ M := fun _ _ => hM _ _
  have ne (r : ℝ) : (fixed (H r) : Set X).Nonempty := by
    obtain ⟨x, hx, _⟩ := nearby C (bound o r)
    exact ⟨x, hx⟩
  choose A hA hproj using fun r => project C (H r) o (ne r)
  let f (r : ℝ) := dist o (A r)
  have hmin (r : ℝ) (y : X) (hy : y ∈ fixed (H r)) : f r ≤ dist o y :=
    (sq_le_sq₀ dist_nonneg dist_nonneg).mp
      ((le_add_of_nonneg_right (sq_nonneg _)).trans (hproj r y hy))
  have sub {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : (fixed (H s) : Set X) ⊆ fixed (H t) :=
    fun _ hx g hg => hx g (hm hs (hs.trans_le hst) hst hg)
  have anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : f t ≤ f s :=
    hmin t (A s) (sub hs hst (hA s))
  obtain ⟨a, ha, hn⟩ := hmoved
  have hfa : 0 < f a := dist_pos.mpr (fun he => hn (he.symm ▸ hA a))
  obtain ⟨b, hb, hb'⟩ := hsmall _ hfa
  obtain ⟨z, hz, hz'⟩ := nearby C (bound o b)
  have hf := ((hmin b z hz).trans hz').trans_lt hb'
  have hab : a < b := lt_of_not_ge fun h => hf.not_ge (anti hb h)
  obtain ⟨r, hr, k, hk, he⟩ := first_displacement ha hab hf
    (fun t _ => hs (A t))
    (fun t _ x hx y hy hxy => displacement_le fun g hg =>
      le_displacement (bound _ x) (hm hx hy hxy hg))
    (fun t ht x htx => displacement_fixed (sub (ha.trans_le ht.1) htx (hA t)))
    (fun t _ => displacement_le (bound _ (a / 2))) (by
      intro s hs t _ hst
      obtain ⟨y, hy, he⟩ := nearby C (bound (A t) s)
      refine ⟨anti (ha.trans_le hs.1) hst, ?_⟩
      exact sub_le_iff_le_add'.mpr ((hmin s y hy).trans
        ((dist_triangle o (A t) y).trans (add_le_add le_rfl he))))
  refine ⟨r, A r, k, ha.trans hr.1, hk, hA r, ?_, he⟩
  intro φ hi hφ hm
  have hd := hproj r (φ (A r)) (hm (hA r))
  rw [show dist o (φ (A r)) = dist o (A r) by rw [← hφ, hi.dist_eq, hφ]] at hd
  exact (dist_eq_zero.mp (by nlinarith : dist (A r) (φ (A r)) = 0)).symm

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

section
/-! # Zooming into the onset of displacement along rational radii -/

namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion

open Filter
open scoped Topology

variable {R : ℝ → ℝ} {r k : ℝ}

theorem Kink.slope (h : Kink R r k) {v z : ℕ → ℝ} {w : ℝ}
    (hv : ∀ n, 0 < v n) (hv0 : Tendsto v atTop (𝓝 0)) (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun n => R (r + v n * z n) / v n) atTop (𝓝 (k * max (-w) 0)) := by
  have hu : Tendsto (fun n => k * max (-z n) 0) atTop (𝓝 (k * max (-w) 0)) :=
    (hz.neg.max tendsto_const_nhds).const_mul k
  have ht : Tendsto (fun n => v n * z n) atTop (𝓝 0) := by simpa using hv0.mul hz
  let M := |w| + 1
  have hM : 0 < M := by unfold M; positivity
  have he : Tendsto (fun n => R (r + v n * z n) / v n - k * max (-z n) 0) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, H⟩ := h (ε / M) (div_pos hε hM)
    filter_upwards [ht.abs.eventually_lt_const (by simpa using hδ),
      hz.abs.eventually_lt_const (show |w| < M by unfold M; linarith)] with n hn hn'
    have hd := H _ hn
    have e : max (-(v n * z n)) 0 = v n * max (-z n) 0 := by
      rw [mul_max_of_nonneg _ _ (hv n).le, mul_neg, mul_zero]
    have a : R (r + v n * z n) / v n - k * max (-z n) 0 =
        (R (r + v n * z n) - k * max (-(v n * z n)) 0) / v n := by
      rw [e, sub_div, mul_left_comm k, mul_div_cancel_left₀ _ (hv n).ne']
    rw [Real.dist_eq, sub_zero, a, abs_div, abs_of_pos (hv n), div_lt_iff₀ (hv n)]
    refine hd.trans_lt ?_
    rw [abs_mul, abs_of_pos (hv n), mul_comm (v n), ← mul_assoc]
    apply mul_lt_mul_of_pos_right _ (hv n)
    exact (mul_lt_mul_of_pos_left hn' (div_pos hε hM)).trans_eq (div_mul_cancel₀ _ hM.ne')
  simpa only [zero_add, sub_add_cancel] using he.add hu

/-- A single choice of rational dilation and origin works for all slopes. -/
theorem Kink.zoom (h : Kink R r k) (hk : 0 < k) :
    ∃ e t : ℕ → ℚ, (∀ n, 0 < e n) ∧ Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n => (t n : ℝ)) atTop (𝓝 r) ∧ ∀ u : ℚ,
        Tendsto (fun n => (2 / (k * e n)) * R ↑(t n + e n * u)) atTop
          (𝓝 (2 * max (1 - (u : ℝ)) 0)) := by
  obtain ⟨e, _, he, he'⟩ := Real.exists_seq_rat_strictAnti_tendsto 0
  choose t hl hu using fun n => exists_rat_btwn (show r - e n < r - e n + (e n : ℝ) ^ 2
    from lt_add_of_pos_right _ (sq_pos_of_pos (he n)))
  let s (n : ℕ) := ((t n : ℝ) - (r - e n)) / e n
  have hs : Tendsto s atTop (𝓝 0) := by
    refine squeeze_zero (fun n => div_nonneg (sub_nonneg.mpr (hl n).le) (he n).le) ?_ he'
    intro n
    exact (div_le_iff₀ (he n)).mpr (by linarith [hu n])
  have heq (n : ℕ) : (t n : ℝ) = r + e n * (s n - 1) := by
    have h' : s n * e n = (t n : ℝ) - (r - e n) := div_mul_cancel₀ _ (he n).ne'
    linarith
  have ht : Tendsto (fun n => (t n : ℝ)) atTop (𝓝 r) := by
    simp only [heq]
    simpa using (he'.mul (hs.sub_const 1)).const_add r
  refine ⟨e, t, fun n => by exact_mod_cast he n, he', ht, fun u => ?_⟩
  have H := (h.slope he he' ((hs.sub_const 1).add_const (u : ℝ))).const_mul (2 / k)
  have ea (n : ℕ) : 2 / (k * e n) * R ↑(t n + e n * u) =
      (2 / k) * (R (r + ↑(e n) * (s n - 1 + (u : ℝ))) / e n) := by
    rw [Rat.cast_add, Rat.cast_mul, heq, mul_add, add_assoc]
    ring
  have ek : (2 / k) * (k * max (-(0 - 1 + (u : ℝ))) 0) = 2 * max (1 - (u : ℝ)) 0 := by
    rw [show -(0 - 1 + (u : ℝ)) = 1 - (u : ℝ) by ring, ← mul_assoc, div_mul_cancel₀ _ hk.ne']
  simp only [ea]
  rwa [ek] at H

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

section
/-!
# Distances of individual leaves

Use two inner arms and one outer arm, all of the same length.
Move the inward radius to the corner of the limiting profile.
The cost of the perturbation on the second inner arm then vanishes.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion
open Filter
open scoped Topology

/-- A scalar squeeze for the distance at a nongeneric parameter. -/
theorem zoom_leaf {R : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    {e t : ℕ → ℚ} {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (he : ∀ n, 0 < e n)
    (he0 : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    (ht : Tendsto (fun n => (t n : ℝ)) atTop (𝓝 r))
    (hlim : ∀ u : ℚ, Tendsto (fun n => f n * R ↑(t n + e n * u)) atTop
      (𝓝 (2 * max (1 - (u : ℝ)) 0)))
    (u : ℚ) (d : ℕ → ℝ)
    (hd : ∀ᶠ n in atTop, 0 ≤ d n ∧ d n ≤ R ↑(t n + e n * u) ∧
      ∀ s : ℚ, 0 < s → s < t n + e n * u →
        3 * R ↑(t n + e n * u) ≤ 2 * R ↑(t n + e n * u + s) + R ↑(t n + e n * u - s) + d n) :
    Tendsto (fun n => f n * d n) atTop (𝓝 (2 * max (1 - (u : ℝ)) 0)) := by
  have hu : ∀ᶠ n in atTop, f n * d n ≤ f n * R ↑(t n + e n * u) :=
    hd.mono fun n hn => mul_le_mul_of_nonneg_left hn.2.1 (hf n)
  rcases le_or_gt 1 u with hge | hlt
  · have h : (1 : ℝ) ≤ u := by exact_mod_cast hge
    have hl := hlim u
    rw [max_eq_right (sub_nonpos.mpr h), mul_zero] at hl ⊢
    exact squeeze_zero' (hd.mono fun n hn => mul_nonneg (hf n) hn.1) hu hl
  let v := 2 * u - 1
  let w (a : ℚ) (n : ℕ) := f n * R ↑(t n + e n * a)
  have hlow : Tendsto (fun n => 3 * w u n - 2 * w 1 n - w v n) atTop
      (𝓝 (2 * max (1 - (u : ℝ)) 0)) := by
    have h := (((hlim u).const_mul 3).sub ((hlim 1).const_mul 2)).sub (hlim v)
    have hv : (v : ℝ) = 2 * u - 1 := by simp [v]
    have hh : (u : ℝ) < 1 := by exact_mod_cast hlt
    convert h using 1
    rw [hv, Rat.cast_one, sub_self, max_self, max_eq_left (by linarith : 0 ≤ 1 - (u : ℝ)),
      max_eq_left (by linarith : 0 ≤ 1 - (2 * (u : ℝ) - 1))]
    congr 1
    ring
  have hrad : Tendsto (fun n => ((t n + e n * v : ℚ) : ℝ)) atTop (𝓝 r) := by
    simpa only [Rat.cast_add, Rat.cast_mul, zero_mul, add_zero] using ht.add (he0.mul_const (v : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow (hlim u) ?_ hu
  filter_upwards [hd, hrad.eventually_const_lt hr] with n hn hv
  let s := e n * (1 - u)
  have h₁ : t n + e n * u + s = t n + e n * 1 := by unfold s; ring
  have h₂ : t n + e n * u - s = t n + e n * v := by unfold s v; ring
  have hpos : 0 < t n + e n * v := by exact_mod_cast hv
  have h := hn.2.2 s (mul_pos (he n) (sub_pos.mpr hlt)) (sub_pos.mp (h₂.symm ▸ hpos))
  rw [h₁, h₂] at h
  unfold w
  linarith only [mul_le_mul_of_nonneg_left h (hf n)]

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

/-!
# The translation groups of valuation disks

Use multiplicative notation for the additive group of the open
valuation disk to apply the metric group-action lemmas.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0

open Filter
open scoped Topology

def disk (E : Type*) [Field E] : AddSubgroup (K0 E) where
  carrier := {z | 0 < val E z}
  zero_mem' := by simp
  add_mem' := (val E).map_lt_add
  neg_mem' {z} h := by simpa using h

abbrev G (E : Type*) [Field E] := Multiplicative (disk E)

variable {E : Type*} [Field E]

def idx (g : G E) : K0 E := (Multiplicative.toAdd g : disk E).val

def shift (z : K0 E) : G E := if h : 0 < val E z then Multiplicative.ofAdd ⟨z, h⟩ else 1

theorem idx_pos (g : G E) : 0 < val E (idx g) := (Multiplicative.toAdd g).property

@[simp] theorem idx_one : idx (1 : G E) = 0 := rfl
@[simp] theorem idx_mul (g h : G E) : idx (g * h) = idx g + idx h := rfl
@[simp] theorem idx_inv (g : G E) : idx g⁻¹ = -idx g := rfl

theorem idx_injective : Function.Injective (idx (E := E)) := by
  intro a b h
  exact Multiplicative.toAdd.injective (Subtype.ext h)

@[simp] theorem idx_shift {z : K0 E} (h : 0 < val E z) : idx (shift z) = z := by
  rw [shift, dite_eq_left h]
  rfl

@[simp] theorem shift_idx (g : G E) : shift (idx g) = g :=
  idx_injective (idx_shift (idx_pos g))

@[simp] theorem shift_zero : shift (0 : K0 E) = 1 := shift_idx 1

theorem shift_add {x y : K0 E} (hx : 0 < val E x) (hy : 0 < val E y) :
    shift (x + y) = shift x * shift y := by
  apply idx_injective
  simp [idx_shift ((val E).map_lt_add hx hy), hx, hy]

def level (E : Type*) [Field E] (r : ℝ) : Subgroup (G E) where
  carrier := {g | ∃ q : ℚ, r ≤ q ∧ ↑q ≤ val E (idx g)}
  one_mem' := by
    obtain ⟨q, hq⟩ := exists_rat_gt r
    exact ⟨q, hq.le, by simp⟩
  inv_mem' := by
    rintro g ⟨q, hq, hm⟩
    exact ⟨q, hq, by simpa using hm⟩
  mul_mem' := by
    rintro a b ⟨p, hp, ha⟩ ⟨q, hq, hb⟩
    refine ⟨min p q, by rw [Rat.cast_min]; exact le_min hp hq, ?_⟩
    exact (val E).map_le_add ((WithTop.coe_le_coe.mpr (min_le_left _ _)).trans ha)
      ((WithTop.coe_le_coe.mpr (min_le_right _ _)).trans hb)

theorem level_anti : Antitone (level E) := by
  rintro s t h g ⟨q, hq, hg⟩
  exact ⟨q, h.trans hq, hg⟩

theorem mem_level (q : ℚ) (g : G E) : g ∈ level E q ↔ ↑q ≤ val E (idx g) := by
  constructor
  · rintro ⟨r, hr, h⟩
    exact (WithTop.coe_le_coe.mpr (Rat.cast_le.mp hr)).trans h
  · exact fun h => ⟨q, le_rfl, h⟩

def zoom (e t₀ : ℚ) (he : 0 < e) (z : K0 E) : K0 E := t t₀ * dilate e he z

theorem val_zoom (e t₀ : ℚ) (he : 0 < e) {z : K0 E} {s : ℚ} (hz : val E z = ↑s) :
    val E (zoom e t₀ he z) = ↑(t₀ + e * s) := by
  simp [zoom, val_dilate, hz]

theorem zoom_pos {r : ℝ} (hr : 0 < r) {e t₀ : ℕ → ℚ} (he : ∀ n, 0 < e n)
    (he0 : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    (ht : Tendsto (fun n => (t₀ n : ℝ)) atTop (𝓝 r)) (z : K0 E) :
    ∀ᶠ n in atTop, 0 < val E (zoom (e n) (t₀ n) (he n) z) := by
  by_cases h : z = 0
  · simp [zoom, h]
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp ((val E).ne_top_iff.mpr h)
  have H : Tendsto (fun n => ((t₀ n + e n * s : ℚ) : ℝ)) atTop (𝓝 r) := by
    simpa only [Rat.cast_add, Rat.cast_mul, zero_mul, add_zero] using ht.add (he0.mul_const (s : ℝ))
  filter_upwards [H.eventually_const_lt hr] with n hn
  rw [val_zoom _ _ _ hs.symm]
  exact_mod_cast hn

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end

/-!
# Wire tests imply radial estimates

Specialization permits using any integral parameter on the left.
There is no need to choose the same generic parameter in every test.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0

variable {E X : Type*} [Field E] [MetricSpace X] [MulAction (G E) X]

def cost (A : X) (z : K0 E) : ℝ := dist A (shift z • A)
def profile (E : Type*) [Field E] [MulAction (G E) X] (A : X) (q : ℝ) : ℝ :=
  displacement (level E q) A

/-- The one-inner-arm and equal-length two-inner-arm distance tests. -/
structure RadialStars (E X : Type*) [Field E] [MetricSpace X] [MulAction (G E) X] : Prop where
  secant : ∀ (A : X) (a b c : ℚ), 0 < a → a < b → b < c → ∀ w : K0 E, 0 ≤ val E w →
    ∃ u : K0 E, 0 ≤ val E u ∧
      ((c : ℝ) - a) * cost A (t b * w) ≤ ((c : ℝ) - b) * cost A (t a * u) + ((b : ℝ) - a) * cost A (t c * u)
  branch : ∀ (A : X) (q s : ℚ), 0 < s → s < q → ∀ w v : K0 E, 0 ≤ val E w → val E v = 0 →
    ∃ u : K0 E, 0 ≤ val E u ∧ 3 * cost A (t q * w) ≤ cost A (t (q + s) * u) +
      cost A (t q * (v + t s * u)) + cost A (t (q - s) * u)

theorem scaled_le (q : ℚ) {z : K0 E} (hz : 0 ≤ val E z) :
    ↑q ≤ val E (t q * z) := by
  rw [AddValuation.map_mul, val_t]
  exact le_add_of_nonneg_right hz

theorem scaled_pos {q : ℚ} (hq : 0 < q) {z : K0 E} (hz : 0 ≤ val E z) :
    0 < val E (t q * z) :=
  (WithTop.coe_pos.mpr hq).trans_le (scaled_le q hz)

theorem unscale (q : ℚ) (z : K0 E) : t q * (t (-q) * z) = z := by
  rw [← mul_assoc, ← t_add, add_neg_cancel, t_zero, one_mul]

theorem le_unscale {q : ℚ} {z : K0 E} (hz : ↑q ≤ val E z) :
    0 ≤ val E (t (-q) * z) := by
  rw [AddValuation.map_mul, val_t]
  have h := add_le_add_right hz ((-q : ℚ) : WithTop ℚ)
  rw [← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero] at h
  exact h

theorem profile_le {A : X} {q : ℚ} {L : ℝ}
    (h : ∀ u : K0 E, 0 ≤ val E u → cost A (t q * u) ≤ L) : profile E A q ≤ L := by
  apply displacement_le
  intro g hg
  have h' := h _ (le_unscale ((mem_level q g).mp hg))
  simpa only [unscale, cost, shift_idx] using h'

theorem cost_le {A : X} {q : ℚ} (hq : 0 < q) {z : K0 E} (hz : ↑q ≤ val E z)
    {M : ℝ} (hM : ∀ x y : X, dist x y ≤ M) : cost A z ≤ profile E A q := by
  apply le_displacement (fun _ _ => hM _ _)
  rw [mem_level, idx_shift ((WithTop.coe_pos.mpr hq).trans_le hz)]
  exact hz

theorem RadialStars.secants (h : RadialStars E X) {M : ℝ}
    (hM : ∀ x y : X, dist x y ≤ M) (A : X) : RationalSecants (profile E A) := by
  intro a b c ha hab hbc
  have h₁ : (a : ℝ) < b := Rat.cast_lt.mpr hab
  have h₂ : (b : ℝ) < c := Rat.cast_lt.mpr hbc
  rw [mul_comm, ← le_div_iff₀ (sub_pos.mpr (h₁.trans h₂))]
  apply profile_le
  intro w hw
  obtain ⟨u, hu, hs⟩ := h.secant A a b c ha hab hbc w hw
  rw [le_div_iff₀ (sub_pos.mpr (h₁.trans h₂)), mul_comm]
  exact hs.trans (add_le_add
    (mul_le_mul_of_nonneg_left (cost_le ha (scaled_le a hu) hM) (sub_nonneg.mpr h₂.le))
    (mul_le_mul_of_nonneg_left (cost_le (ha.trans (hab.trans hbc)) (scaled_le c hu) hM)
      (sub_nonneg.mpr h₁.le)))

variable [IsIsometricSMul (G E) X]

theorem cost_add (A : X) {a b : K0 E} (ha : 0 < val E a) (hb : 0 < val E b) :
    cost A (a + b) ≤ cost A a + cost A b := by
  unfold cost
  rw [shift_add ha hb, mul_smul]
  simpa only [dist_smul] using dist_triangle A (shift a • A) (shift a • shift b • A)

theorem RadialStars.star (h : RadialStars E X) {M : ℝ} (hM : ∀ x y : X, dist x y ≤ M)
    (A : X) {q s : ℚ} (hs : 0 < s) (hsq : s < q) {z : K0 E} (hz : val E z = ↑q) :
    3 * profile E A q ≤ 2 * profile E A ↑(q + s) + profile E A ↑(q - s) + cost A z := by
  have hq := hs.trans hsq
  let v := t (-q) * z
  have hv : val E v = 0 := by
    unfold v
    rw [AddValuation.map_mul, val_t, hz, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero]
  rw [mul_comm 3, ← le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
  apply profile_le
  intro w hw
  obtain ⟨u, hu, h'⟩ := h.branch A q s hs hsq w v hw hv
  have heq : t q * (v + t s * u) = z + t (q + s) * u := by
    rw [mul_add, t_add, mul_assoc, show t q * v = z from unscale q z]
  rw [heq] at h'
  have he := cost_add A (hz.symm ▸ WithTop.coe_pos.mpr hq) (scaled_pos (add_pos hq hs) hu)
  have hi := cost_le (A := A) (add_pos hq hs) (scaled_le (q + s) hu) hM
  have ho := cost_le (A := A) (sub_pos.mpr hsq) (scaled_le (q - s) hu) hM
  linarith only [h', he, hi, ho]

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end

/-! The generic rate and comparisons along a single arm. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0

variable {F : Type} [Field F] {E : Type*} [Field E]

structure Branches (E : Type*) [Field E] where
  pos : Four (K0 E)
  integral : ∀ i, 0 ≤ val E (pos i)
  separate : ∀ i j, i ≠ j → val E (pos i - pos j) = 0

instance [Infinite E] : Nonempty (Branches E) := by
  let e := Infinite.natEmbedding E
  refine ⟨fun i => C (e i.val), fun i => ?_, fun i j h => ?_⟩
  · by_cases h : e i.val = 0 <;> simp [h]
  · rw [← map_sub, val_C (sub_ne_zero.mpr (e.injective.ne (Fin.val_injective.ne h)))]

namespace Branches

variable (B : Branches E) (H : MotionTree F E)

def pts (z : K0 E) : Four (K0 E) := fun i => if i = 3 then z else B.pos i

def rate (z : K0 E) (l : Four ℚ) := H.rate (B.pts z) l

theorem rate_nonneg (z : K0 E) (l : Four ℚ) (hl : ∀ i, l i ≤ 1) :
    0 ≤ B.rate H z l := H.nonneg _ _ hl

theorem bound {z : K0 E} (h : 0 ≤ val E z) {l : ℚ} (hl : 0 ≤ l) (hl' : l ≤ 1) :
    B.rate H z (fun _ => l) ≤ 6 * (l : ℝ) := by
  have hi (i) : 0 ≤ val E (B.pts z i) := by unfold pts; split <;> first | exact h | exact B.integral _
  have hb (i j) : diskGap (B.pts z i) (B.pts z j) l l ≤ 2 * l := by
    have he := gap_bound hl hl zero_le_one
      ((le_min (hi i) (hi j)).trans ((val E).map_sub _ _))
    linarith
  refine (H.path _ _ (fun _ => hl') 0 1 2 3 (by decide)).trans ?_
  exact_mod_cast (show diskGap (B.pts z 0) (B.pts z 1) l l +
    diskGap (B.pts z 1) (B.pts z 2) l l + diskGap (B.pts z 2) (B.pts z 3) l l ≤ 6 * l by
    linarith only [hb 0 1, hb 1 2, hb 2 3])

def generic (l : ℚ) := sSup {r | ∃ z, 0 ≤ val E z ∧ B.rate H z (fun _ => l) = r}

theorem generic_le {l : ℚ} {D : ℝ} (h : ∀ z, 0 ≤ val E z → B.rate H z (fun _ => l) ≤ D) :
    B.generic H l ≤ D :=
  csSup_le ⟨_, 0, by simp, rfl⟩ (by rintro _ ⟨z, hz, rfl⟩; exact h z hz)

theorem le_generic {l : ℚ} (hl : 0 ≤ l) (hl' : l ≤ 1) {z : K0 E} (hz : 0 ≤ val E z) :
    B.rate H z (fun _ => l) ≤ B.generic H l :=
  le_csSup ⟨_, by rintro _ ⟨z, hz, rfl⟩; exact B.bound H hz hl hl'⟩ ⟨z, hz, rfl⟩

def X (l : ℚ) := B.generic H l / (2 * (l : ℝ))

theorem generic_eq {l : ℚ} (hl : 0 < l) : B.generic H l = 2 * (l : ℝ) * B.X H l := by
  unfold X
  rw [mul_div_cancel₀ _ (by positivity)]

private theorem radial {l L : ℚ} (hl : 0 < l) (h : l ≤ L) (hL : L ≤ 1)
    {z : K0 E} (hz : 0 ≤ val E z) :
    B.rate H z (fun _ => l) ≤ (l : ℝ) / L * B.rate H z (fun _ => L) := by
  have hp := hl.trans_le h
  have hch := H.chord (B.pts z) (B.pts z) (B.pts z) (fun _ => 0) (fun _ => L) (fun _ => l)
    (fun _ => zero_le_one) (fun _ => hL) (fun _ => h.trans hL) (l / L) (by positivity)
    ((div_le_one hp).mpr h) (fun i => by
      rw [gap_same _ hl.le zero_le_one, gap_same _ hp.le zero_le_one, sub_zero, sub_zero,
        div_mul_cancel₀ _ hp.ne']) (fun i => by
      rw [gap_same _ h (h.trans hL), gap_same _ hp.le zero_le_one, sub_zero, sub_mul, one_mul,
        div_mul_cancel₀ _ hp.ne'])
  have hzero : H.rate (B.pts z) (fun _ => 0) = 0 := le_antisymm
    (by simpa [rate] using B.bound H hz (l := 0) le_rfl zero_le_one) (H.nonneg _ _ fun _ => zero_le_one)
  simpa only [hzero, mul_zero, zero_add, Rat.cast_div, rate] using hch

theorem monotone_X : MonotoneOn (B.X H) (Set.Ioc 0 1) := by
  intro l hl L hL h
  have hbound : B.generic H l ≤ (l : ℝ) / L * B.generic H L := by
    refine B.generic_le H fun z hz => (B.radial H hl.1 h hL.2 hz).trans ?_
    exact mul_le_mul_of_nonneg_left (B.le_generic H hL.1.le hL.2 hz)
      (div_nonneg (Rat.cast_nonneg.mpr hl.1.le) (Rat.cast_nonneg.mpr hL.1.le))
  rw [B.generic_eq H hl.1, B.generic_eq H hL.1] at hbound
  have hpos : (0 : ℝ) < L := by exact_mod_cast hL.1
  have he : (l : ℝ) / L * (2 * L * B.X H L) = 2 * l * B.X H L := by field_simp
  rw [he] at hbound
  exact le_of_mul_le_mul_left hbound (mul_pos (by norm_num) (Rat.cast_pos.mpr hl.1))

theorem star {n : ℕ} (a b : K0 E) (c : Fin n → K0 E)
    (hc : ∀ j, 0 ≤ val E (c j)) (hd : ∀ i j, i ≠ j → val E (c i - c j) = 0)
    (r : Option (Fin n) → ℚ) (hr : ∀ j, 0 < r j)
    (l : Four ℚ) (k : Option (Fin n) → Four ℚ)
    (hl : ∀ i, l i ≤ 1) (hk : ∀ j i, k j i ≤ 1)
    (harmonic : ∀ i, ∑ j, (k j i - l i) / r j = 0) (v : K0 E) (hv : 0 ≤ val E v) :
    ∃ u : Option (Fin n) → K0 E, (∀ j, 0 ≤ val E (u j)) ∧
      0 ≤ ∑ j, (B.rate H (a + b * armEnd c r (u j) j) (k j) - B.rate H (a + b * v) l) / (r j : ℝ) := by
  let w : Four (K0 E) := fun i => if i = 3 then b else 0
  have he (u : K0 E) : diskAffine (B.pts a) w u = B.pts (a + b * u) := by
    funext i
    by_cases hi : i = 3 <;> simp [hi, diskAffine, pts, w]
  simpa only [he, rate] using H.star (B.pts a) w c hc hd r hr l k hl hk harmonic v hv

theorem ray {a : K0 E} {r t₁ t₂ : ℚ} (h₁ : 0 < t₁) (h₂ : 0 < t₂)
    (l k m : Four ℚ) (hl : ∀ i, l i ≤ 1) (hk : ∀ i, k i ≤ 1) (hm : ∀ i, m i ≤ 1)
    (harmonic : ∀ i, (k i - l i) * t₂ + (m i - l i) * t₁ = 0)
    {v : K0 E} (hv : 0 ≤ val E v) :
    ∃ u w : K0 E, 0 ≤ val E u ∧ 0 ≤ val E w ∧
      ((t₁ : ℝ) + t₂) * B.rate H (a + t r * v) l ≤
        t₂ * B.rate H (a + t (r + t₁) * u) k + t₁ * B.rate H (a + t (r - t₂) * w) m := by
  let s : Option (Fin 1) → ℚ := fun j => j.elim t₂ (fun _ => t₁)
  let d : Option (Fin 1) → Four ℚ := fun j => j.elim m (fun _ => k)
  have he i : ∑ j, (d j i - l i) / s j = 0 := by
    simp only [Fintype.sum_option, Fin.sum_univ_one, s, d, Option.elim_none, Option.elim_some]
    field_simp
    linarith only [harmonic i]
  obtain ⟨u, hu, hw⟩ := B.star H a (t r) (fun _ : Fin 1 => 0) (by simp)
    (fun i j h => (h (Subsingleton.elim _ _)).elim) s (by rintro (_|j) <;> assumption) l d hl
    (by rintro (_|j) <;> assumption) he v hv
  refine ⟨u (some 0), u none, hu _, hu _, ?_⟩
  simp only [Fintype.sum_option, Fin.sum_univ_one, s, d, Option.elim_none, Option.elim_some, armEnd,
    zero_add, ← mul_assoc, ← t_add, ← sub_eq_add_neg] at hw
  have h₁' : (0 : ℝ) < t₁ := Rat.cast_pos.mpr h₁
  have h₂' : (0 : ℝ) < t₂ := Rat.cast_pos.mpr h₂
  field_simp at hw
  linarith only [hw]

end Branches
end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end

/-! The three collision arms and their two-pair endpoints. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0.Branches

open Spectral
variable {F : Type} [Field F] {E : Type*} [Field E] (B : Branches E) (H : MotionTree F E)

def depth (j : Fin 4) (l r : ℚ) : Four ℚ :=
  fun i => if i = j ∨ i = 3 then l + r / 2 else l - r / 2

theorem depth_le (j : Fin 4) {l r : ℚ} (hu : l ≤ 1 / 2) (h : r ∈ Set.Icc 0 (2 * l)) :
    ∀ i, depth j l r i ≤ 1 := by
  intro i
  unfold depth
  split <;> linarith [h.1, h.2]

theorem merged (j : Fin 4) (hj : j ≠ 3) {l : ℚ} (hl : l ∈ Set.Ioc 0 (1 / 2))
    (u : K0 E) (hu : 0 ≤ val E u) :
    B.rate H (B.pos j + t (2 * l) * u) (depth j l (2 * l)) ≤ 2 * (l : ℝ) := by
  obtain ⟨a, b, ha, hb, ha', hb', he⟩ :
      ∃ a b : Fin 4, a ≠ j ∧ b ≠ j ∧ a ≠ 3 ∧ b ≠ 3 ∧ ({a, b, j, 3} : Finset (Fin 4)) = Finset.univ := by
    fin_cases j
    · exact ⟨1, 2, by decide⟩
    · exact ⟨0, 2, by decide⟩
    · exact ⟨0, 1, by decide⟩
    · exact (hj rfl).elim
  let z := B.pos j + t (2 * l) * u
  have hL : 2 * l ≤ 1 := by linarith [hl.2]
  have hpos : 0 ≤ 2 * l := by linarith [hl.1]
  have hab : diskGap (B.pos a) (B.pos b) 0 0 = 0 := by
    rw [gap_of_le le_rfl ((le_min (B.integral a) (B.integral b)).trans ((val E).map_sub _ _))
      zero_le_one, sub_self]
  have hbj : diskGap (B.pos b) (B.pos j) 0 (2 * l) = 2 * l := by
    rw [gap_of_le hpos (by simp [B.separate b j hb]) zero_le_one, sub_zero]
  have hjz : diskGap (B.pos j) z (2 * l) (2 * l) = 0 := by
    rw [gap_symm, gap_of_le le_rfl (by simpa [z] using scaled_le (2 * l) hu) hL, sub_self]
  have hp := H.path (B.pts z) (depth j l (2 * l)) (depth_le j hl.2 ⟨hpos, le_rfl⟩) a b j 3 he
  simpa [pts, depth, ha, hb, ha', hb', hj, ← two_mul, hab, hbj, hjz, rate] using hp

private theorem displacement (i j : Fin 4) (hij : i ≠ j) {r : ℚ} (hr : 0 < r) :
    val E (B.pos i - (B.pos j + t r)) = 0 := by
  rw [show B.pos i - (B.pos j + t r) = (B.pos i - B.pos j) + (-t r) by ring]
  have h : val E (B.pos i - B.pos j) < val E (-t r) := by
    rw [B.separate i j hij, AddValuation.map_neg, val_t]
    exact WithTop.coe_pos.mpr hr
  rw [AddValuation.map_add_of_distinct_val _ h.ne, min_eq_left h.le, B.separate i j hij]

theorem collision_point {l h : ℚ} (hl : l ∈ Set.Ioc 0 (1 / 2)) (hh : h ∈ Set.Ioc 0 (2 * l)) :
    ∃ z : K0 E, val E (B.pos 0 - z) = 0 ∧ val E (B.pos 1 - z) = 0 ∧ val E (B.pos 2 - z) = ↑(2 * l - h) ∧
      B.rate H z (depth 2 l (2 * l - h)) ≤ 2 * (l : ℝ) + h * (B.X H l - 1) := by
  let r := 2 * l - h
  have hr : 0 ≤ r := sub_nonneg.mpr hh.2
  have hu : r ≤ 2 * l := sub_le_self _ hh.1.le
  let k := depth 2 l r
  have hk : ∀ i, k i ≤ 1 := depth_le _ hl.2 ⟨hr, hu⟩
  have hl' : l ≤ 1 := by linarith [hl.2]
  change ∃ z, _ ∧ _ ∧ val E (B.pos 2 - z) = ↑r ∧ B.rate H z k ≤ _
  rcases hr.eq_or_lt with he | he
  · have hk₀ : k = fun _ => l := by ext; simp [k, depth, ← he]
    refine ⟨B.pos 3, B.separate _ _ (by decide), B.separate _ _ (by decide), by simp [← he, B.separate 2 3 (by decide)], ?_⟩
    rw [hk₀, show h = 2 * l by unfold r at he; linarith]
    have H' := B.le_generic H hl.1.le hl' (B.integral 3)
    rw [B.generic_eq H hl.1] at H'
    push_cast
    linarith only [H']
  · refine ⟨B.pos 2 + t r, B.displacement 0 2 (by decide) he, B.displacement 1 2 (by decide) he, by simp, ?_⟩
    obtain ⟨u, w, hu', hw, e⟩ := B.ray H (a := B.pos 2) (r := r) hh.1 he k (depth 2 l (2 * l))
      (fun _ => l) hk (depth_le _ hl.2 ⟨by linarith [hl.1], le_rfl⟩) (fun _ => hl')
      (fun i => by unfold k depth; split <;> unfold r <;> ring) (v := 1) (by simp)
    rw [show r + h = 2 * l by unfold r; ring, sub_self, t_zero, one_mul, mul_one] at e
    have h₁ := B.merged H 2 (by decide) hl u hu'
    have h₂ := B.le_generic H hl.1.le hl' ((le_min (B.integral 2) hw).trans ((val E).map_add _ _))
    rw [B.generic_eq H hl.1] at h₂
    have hi := e.trans (add_le_add (mul_le_mul_of_nonneg_left h₁ (Rat.cast_nonneg.mpr hr))
      (mul_le_mul_of_nonneg_left h₂ (Rat.cast_nonneg.mpr hh.1.le)))
    refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < 2 * l by exact_mod_cast (show 0 < 2 * l by linarith [hl.1]))
    rw [show (r : ℝ) = 2 * l - h by simp [r]] at hi
    linarith only [hi]


end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0.Branches
end

/-! A shrinking outer arm is controlled by a larger generic placement. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0.Branches

variable {F : Type} [Field F] {E : Type*} [Field E] (B : Branches E) (H : MotionTree F E)

def outer (l r : ℚ) : Four ℚ := fun i => if i = 3 then l - 2 * r else l

def Y (l : ℚ) := B.rate H 0 (outer l l) / (2 * (l : ℝ))

theorem outer_le {l r : ℚ} (hl : l ≤ 1) (hr : 0 ≤ r) : ∀ i, outer l r i ≤ 1 := by
  intro i
  unfold outer
  split <;> linarith

theorem outer_bound {l : ℚ} (hl : l ∈ Set.Ioc 0 1) :
    B.rate H 0 (outer l l) ≤ 6 * (l : ℝ) := by
  have hh (i j : Fin 4) : diskGap (B.pos i) (B.pos j) l l ≤ 2 * l := by
    have e := gap_bound hl.1.le hl.1.le zero_le_one
      ((le_min (B.integral i) (B.integral j)).trans ((val E).map_sub _ _))
    linarith
  have h : diskGap (B.pos 2) 0 l (-l) ≤ 2 * l := by
    have hv : ((-l : ℚ) : WithTop ℚ) ≤ val E (B.pos 2 - 0) := by
      rw [sub_zero]
      exact (WithTop.coe_le_coe.mpr (neg_nonpos.mpr hl.1.le)).trans (B.integral _)
    have := gap_bound (by linarith [hl.1] : -l ≤ l) le_rfl (by linarith [hl.1]) hv
    linarith
  have hp := H.path (B.pts 0) (outer l l) (outer_le hl.2 hl.1.le) 0 1 2 3 (by decide)
  change B.rate H 0 (outer l l) ≤
    (diskGap (B.pos 0) (B.pos 1) l l + diskGap (B.pos 1) (B.pos 2) l l +
      diskGap (B.pos 2) 0 l (l - 2 * l) : ℚ) at hp
  rw [show l - 2 * l = -l by ring] at hp
  exact hp.trans (by exact_mod_cast (show _ ≤ 6 * l by linarith only [hh 0 1, hh 1 2, h]))

theorem outer_merge {l : ℚ} (hl : l ∈ Set.Ioc 0 1) (u : K0 E) (hu : 0 ≤ val E u) :
    B.rate H (t (-l) * u) (outer l l) ≤ B.rate H 0 (outer l l) := by
  apply H.same _ _ _ (outer_le hl.2 hl.1.le)
  intro i
  by_cases hi : i = 3
  · simpa only [pts, outer, ite_eq_left hi, sub_zero, show l - 2 * l = -l by ring] using scaled_le (-l) hu
  · simp [pts, hi]

private theorem outer_radial {l L : ℚ} (hl : 0 < l) (h : l < L) (hL : L ≤ 1) :
    B.rate H 0 (outer l l) ≤ (l : ℝ) / L * B.rate H (t (-l)) (outer L l) := by
  have hp := hl.trans h
  have hl' := h.le.trans hL
  have h₁ (i : Fin 4) : diskGap (B.pts 0 i) (B.pts 0 i) 0 (outer l l i) = l := by
    by_cases hi : i = 3
    · rw [outer, ite_eq_left hi, gap_symm, gap_same _ (by linarith) (by linarith)]
      ring
    · rw [outer, ite_eq_right hi, gap_same _ hl.le zero_le_one, sub_zero]
  have hv : val E (0 - t (-l)) = ↑(-l) := by rw [zero_sub, AddValuation.map_neg, val_t]
  have h₂ (i : Fin 4) : diskGap (B.pts 0 i) (B.pts (t (-l)) i) 0 (outer L l i) = L := by
    by_cases hi : i = 3
    · simp only [pts, outer, ite_eq_left hi]
      rw [gap_branch (by linarith) (by linarith) hv]
      ring
    · simp only [pts, outer, ite_eq_right hi, gap_same _ hp.le zero_le_one, sub_zero]
  have h₃ (i : Fin 4) :
      diskGap (B.pts 0 i) (B.pts (t (-l)) i) (outer l l i) (outer L l i) = L - l := by
    by_cases hi : i = 3
    · simp only [pts, outer, ite_eq_left hi]
      rw [gap_branch (by linarith) (by linarith) hv]
      ring
    · simp only [pts, outer, ite_eq_right hi, gap_same _ h.le hl']
  have hch := H.chord (B.pts 0) (B.pts (t (-l))) (B.pts 0) (fun _ => 0) (outer L l) (outer l l)
    (fun _ => zero_le_one) (outer_le hL hl.le) (outer_le hl' hl.le) (l / L)
    (by positivity) ((div_le_one hp).mpr h.le)
    (fun i => by rw [h₁, h₂, div_mul_cancel₀ _ hp.ne'])
    (fun i => by rw [h₃, h₂, sub_mul, one_mul, div_mul_cancel₀ _ hp.ne'])
  have he : H.rate (B.pts 0) (fun _ => 0) = 0 := le_antisymm
    (by simpa [rate] using B.bound H (z := 0) (by simp) (l := 0) le_rfl zero_le_one)
    (H.nonneg _ _ fun _ => zero_le_one)
  simpa only [he, mul_zero, zero_add, Rat.cast_div, rate] using hch

theorem negative_limit {L : ℚ} (hL : L ∈ Set.Ioc 0 1) (δ : ℝ) (hd : 0 < δ) :
    ∃ r : ℚ, 0 < r ∧ ∀ l ∈ Set.Ioc 0 r, B.Y H l ≤ B.X H L + δ := by
  have hpos : (0 : ℝ) < L := Rat.cast_pos.mpr hL.1
  obtain ⟨r, hr, hr'⟩ := exists_rat_btwn (lt_min hpos (by positivity : (0 : ℝ) < L * δ / 3))
  refine ⟨r, Rat.cast_pos.mp hr, fun l hl => ?_⟩
  have he := (Rat.cast_le.mpr hl.2 : (l : ℝ) ≤ r).trans_lt hr'
  have h : l < L := Rat.cast_lt.mp (he.trans_le (min_le_left _ _))
  have hs : (l : ℝ) < L * δ / 3 := he.trans_le (min_le_right _ _)
  have hp : (0 : ℝ) < l := Rat.cast_pos.mpr hl.1
  obtain ⟨u, v, hu, hv, hb⟩ := B.ray H (a := 0) (r := -l) hl.1 (sub_pos.mpr h)
    (outer L l) (fun _ => L) (outer L L) (outer_le hL.2 hl.1.le) (fun _ => hL.2)
    (outer_le hL.2 hL.1.le) (fun i => by unfold outer; split <;> ring) (v := 1) (by simp)
  simp only [zero_add, mul_one, neg_add_cancel, t_zero, one_mul, show -l - (L - l) = -L by ring,
    Rat.cast_sub, add_sub_cancel] at hb
  have hi := B.le_generic H hL.1.le hL.2 hu
  have hj := (B.outer_merge H hL v hv).trans (B.outer_bound H hL)
  have hx : 0 ≤ B.generic H L := (B.rate_nonneg H _ _ (fun _ => hL.2)).trans hi
  have hu' := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr (Rat.cast_le.mpr h.le : (l : ℝ) ≤ L))
  have hv' := mul_le_mul_of_nonneg_left hj hp.le
  have hm : B.rate H (t (-l)) (outer L l) ≤ B.generic H L + 6 * l := by
    refine le_of_mul_le_mul_left ?_ hpos
    linarith only [hb, hu', hv', mul_nonneg hp.le hx]
  have hb' := (B.outer_radial H hl.1 h hL.2).trans
    (mul_le_mul_of_nonneg_left hm (div_nonneg hp.le hpos.le))
  rw [B.generic_eq H hL.1] at hb'
  unfold Y
  rw [div_le_iff₀ (by positivity)]
  refine hb'.trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  linarith only [mul_le_mul_of_nonneg_left hs.le hp.le]

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0.Branches
end

/-! Applying the submean test on the collision, unused, and outer arms. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0

variable {F : Type} [Field F] {E : Type*} [Field E]

namespace Branches

variable (B : Branches E) (H : MotionTree F E)

private def lengths (l : ℚ) : Option (Fin 4) → ℚ
  | none => l
  | some j => if j = 3 then l else 2 * l

private def depths (l : ℚ) : Option (Fin 4) → Four ℚ
  | none => outer l l
  | some j => if j = 3 then fun _ => 3 * l / 2 else depth j l (2 * l)

private theorem weights {l : ℚ} (hl : 0 < l) (i : Fin 4) :
    ∑ j, (depths l j i - l) / lengths l j = 0 := by
  rw [Fintype.sum_option, Fin.sum_univ_four]
  fin_cases i <;> simp [depths, lengths, depth, outer] <;> field_simp <;> ring

private theorem scalar_star {l a b c d e f : ℝ} (hl : 0 < l)
    (h : 0 ≤ (b - a) / l + ((c - a) / (2 * l) + (d - a) / (2 * l) + (e - a) / (2 * l) + (f - a) / l)) :
    7 * a ≤ 2 * b + c + d + e + 2 * f := by
  field_simp at h
  linarith only [h]

theorem five_arms {l : ℚ} (hl : l ∈ Set.Ioc 0 (1 / 2)) :
    7 * B.X H l ≤ 3 + 2 * B.Y H l + 3 * B.X H (3 * l / 2) := by
  have hl' : l ∈ Set.Ioc 0 1 := ⟨hl.1, by linarith [hl.2]⟩
  have hL : 3 * l / 2 ∈ Set.Ioc 0 1 := ⟨by linarith [hl.1], by linarith [hl.2]⟩
  have hp : (0 : ℝ) < l := Rat.cast_pos.mpr hl.1
  have hr : ∀ j, 0 < lengths l j := by
    rintro (_|j)
    · exact hl.1
    · simp only [lengths]
      split <;> linarith [hl.1]
  have hk : ∀ j i, depths l j i ≤ 1 := by
    rintro (_|j) i
    · exact outer_le hl'.2 hl.1.le _
    · simp only [depths]
      split
      · exact hL.2
      · exact depth_le _ hl.2 ⟨by linarith [hl.1], le_rfl⟩ _
  have h : B.generic H l ≤ (2 * B.rate H 0 (outer l l) + 6 * l + 2 * B.generic H (3 * l / 2)) / 7 := by
    apply B.generic_le H
    intro v hv
    obtain ⟨u, hu, he⟩ := B.star H 0 1 B.pos B.integral B.separate (lengths l) hr
      (fun _ => l) (depths l) (fun _ => hl'.2) hk (weights hl.1) v hv
    simp only [Fintype.sum_option, Fin.sum_univ_four, one_mul, zero_add,
      armEnd, lengths, depths, Fin.reduceEq, ↓reduceIte, Rat.cast_mul, Rat.cast_ofNat] at he
    have h₀ := B.merged H 0 (by decide) hl _ (hu (some 0))
    have h₁ := B.merged H 1 (by decide) hl _ (hu (some 1))
    have h₂ := B.merged H 2 (by decide) hl _ (hu (some 2))
    have h₃ := B.le_generic H hL.1.le hL.2
      ((le_min (B.integral 3) (scaled_pos hl.1 (hu (some 3))).le).trans ((val E).map_add _ _))
    have h₄ := B.outer_merge H hl' _ (hu none)
    linarith only [scalar_star hp he, h₀, h₁, h₂, h₃, h₄]
  rw [B.generic_eq H hl.1, B.generic_eq H hL.1,
    show B.rate H 0 (outer l l) = 2 * (l : ℝ) * B.Y H l by unfold Y; rw [mul_div_cancel₀ _ (by positivity)]] at h
  push_cast at h
  exact le_of_mul_le_mul_left (by linarith only [h]) hp

/-- The common label near the branch point has normalized price at most
three halves in the limit. An infimum avoids any derivative assumptions. -/
theorem small_X {ε : ℝ} (hε : 0 < ε) :
    ∃ l ∈ Set.Ioc 0 (1 / 2 : ℚ), B.X H l ≤ 3 / 2 + ε := by
  by_contra! lower
  let S := B.X H '' Set.Ioc 0 (1 / 2 : ℚ)
  have hs : S.Nonempty := ⟨_, 1 / 2, ⟨by norm_num, le_rfl⟩, rfl⟩
  have hb : 3 / 2 + ε ∈ lowerBounds S := by
    rintro _ ⟨l, hl, rfl⟩
    exact (lower l hl).le
  have he := le_csInf hs hb
  obtain ⟨_, ⟨t, ht, rfl⟩, hsmall⟩ := exists_lt_of_csInf_lt hs
    (show sInf S < sInf S + ε / 4 by linarith)
  have ht' : t ∈ Set.Ioc 0 (1 : ℚ) := ⟨ht.1, by linarith [ht.2]⟩
  obtain ⟨r, hr, hr'⟩ := B.negative_limit H ht' (ε / 4) (by positivity)
  let l := min (t / 3) r
  have hl : 0 < l := lt_min (by linarith [ht.1]) hr
  have hu : l ≤ t / 3 := min_le_left _ _
  have hlt : l ∈ Set.Ioc 0 (1 / 2 : ℚ) := ⟨hl, by linarith [ht.2]⟩
  have hi : sInf S ≤ B.X H l := csInf_le ⟨_, hb⟩ ⟨l, hlt, rfl⟩
  have hy := hr' l ⟨hl, min_le_right _ _⟩
  have hx := B.monotone_X H (show 3 * l / 2 ∈ Set.Ioc 0 (1 : ℚ) by constructor <;> linarith [ht.2]) ht'
    (show 3 * l / 2 ≤ t by linarith)
  linarith only [B.five_arms H hlt, hy, hx, hi, he, hsmall, hε]

end Branches

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end
