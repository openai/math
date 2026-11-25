import OAI.LinearAlgebra.MatrixExponent.Rectangle.Rows
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Scale
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Pairing
import OAI.LinearAlgebra.MatrixExponent.Prices.Fields
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import OAI.LinearAlgebra.MatrixExponent.UpperBound
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Face.Contact
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Arms
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi.Count

section
/-! # Passing discrete concavity and tripling to a continuum profile -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Filter Set
open scoped Topology

private theorem secants {f g : ℕ → ℝ} {m i j k : ℕ} (h : Row f g m)
    (hij : i ≤ j) (hjk : j ≤ k) :
    (f k - f j) * ((j : ℝ) - i) ≤ (f j - f i) * ((k : ℝ) - j) := by
  have hl := (TensorSpectrum.row_secant_bounds f h.dec i (j - i)).2
  have hu := (TensorSpectrum.row_secant_bounds f h.dec j (k - j)).1
  rw [Nat.add_sub_of_le hij, Nat.cast_sub hij] at hl
  rw [Nat.add_sub_of_le hjk, Nat.cast_sub hjk] at hu
  linarith only [mul_le_mul_of_nonneg_right hl (sub_nonneg.mpr (Nat.cast_le.mpr hjk : (j : ℝ) ≤ k)),
    mul_le_mul_of_nonneg_right hu (sub_nonneg.mpr (Nat.cast_le.mpr hij : (i : ℝ) ≤ j))]

theorem curve_limit {f g : ℝ → ℕ → ℝ} {F G : ℝ → ℝ} {a : ℝ} {m : ℝ → ℕ} {q : ℝ → ℝ}
    (ha : 0 < a) (hm : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 a))
    (hq : ∀ n, 0 < n → 0 < q n) (hr : ∀ n, Row (f n) (g n) (m n))
    (hF : ∀ x, 0 < x → 0 < F x)
    (hf : ∀ x, 0 < x → ∀ k : ℝ → ℕ, Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 x) →
      Tendsto (fun n => f n (k n) / q n) atTop (𝓝 (F x)))
    (hg : ∀ x, 0 < x → ∀ k : ℝ → ℕ, Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 x) →
      Tendsto (fun n => g n (k n) / q n) atTop (𝓝 (G x))) : Curve F G a := by
  let L (x n : ℝ) := ⌊x * n⌋₊
  have hL {x} (hx : 0 < x) : Tendsto (fun n => (L x n : ℝ) / n) atTop (𝓝 x) :=
    tendsto_nat_floor_mul_div_atTop hx.le
  have hfl {x} (hx : 0 < x) := hf x hx _ (hL hx)
  refine ⟨hF, ?_, ?_⟩
  · apply concaveOn_of_slope_anti_adjacent (convex_Ioi 0)
    intro x y z hx hz hxy hyz
    have hy := lt_trans (show 0 < x from hx) hxy
    rw [div_le_div_iff₀ (sub_pos.mpr hyz) (sub_pos.mpr hxy)]
    apply le_of_tendsto_of_tendsto (((hfl hz).sub (hfl hy)).mul ((hL hy).sub (hL hx)))
      (((hfl hy).sub (hfl hx)).mul ((hL hz).sub (hL hy)))
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    have h₁ : L x n ≤ L y n := Nat.floor_mono (mul_le_mul_of_nonneg_right hxy.le hn.le)
    have h₂ : L y n ≤ L z n := Nat.floor_mono (mul_le_mul_of_nonneg_right hyz.le hn.le)
    simp only [← sub_div, div_mul_div_comm]
    exact div_le_div_of_nonneg_right (secants (hr n) h₁ h₂) (mul_nonneg (hq n hn).le hn.le)
  · intro x hx
    let k n := 3 * L x n + m n + 2
    have hk : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 (3 * x + a)) := by
      have h₂ : Tendsto (fun n : ℝ => 2 / n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
      simpa only [k, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_div, mul_div_assoc, add_zero]
        using (((hL hx).const_mul 3).add hm).add h₂
    apply le_of_tendsto_of_tendsto (((hfl hx).const_mul 2).add (hg x hx _ (hL hx)))
      (hf _ (by positivity) k hk)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    rw [← mul_div_assoc, ← add_div]
    exact div_le_div_of_nonneg_right ((hr n).trip _) (hq n hn).le

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

section
/-! # A derivative from comparison with equal-cost energy increments -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
open Set Filter
open scoped Topology

variable {f g : ℝ → ℝ} {a b d x : ℝ}

private theorem profile_derivative (c d x y : ℝ) (hc : 0 < c) :
    HasDerivAt (fun t => y - c * d * Real.log (1 + (t - x) / c)) (-d) x := by
  have h := (((hasDerivAt_id x).sub_const x).div_const c).const_add 1
  have h' := (h.log (by simp)).const_mul (c * d)
  convert! h'.const_sub y using 1
  simp only [id_eq, sub_self, zero_div, add_zero, div_one]
  field_simp

theorem right_derivative (ha : 0 < a) (hb : 0 < b)
    (h : ∀ u : ℝ, 0 < u →
      a * d * Real.log (1 + u / a) ≤ f x - f (x + u) ∧ f x - f (x + u) ≤ b * d * Real.log (1 + u / b)) :
    HasDerivWithinAt f (-d) (Ioi x) x := by
  let p c t := f x - c * d * Real.log (1 + (t - x) / c)
  have he c : p c x = f x := by simp [p]
  have ht c (hc : 0 < c) := hasDerivWithinAt_iff_tendsto_slope.mp
    ((profile_derivative c d x (f x) hc).hasDerivWithinAt (s := Ioi x))
  have hs (t : ℝ) (ht : x < t) :
      slope (p b) x t ≤ slope f x t ∧ slope f x t ≤ slope (p a) x t := by
    obtain ⟨h₁, h₂⟩ := h (t - x) (sub_pos.mpr ht)
    rw [show x + (t - x) = t by ring] at h₁ h₂
    simp only [slope_def_field, he]
    constructor <;> apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr ht.le) <;>
      unfold p <;> linarith
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (ht b hb) (ht a ha) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t h; exact (hs t h.1).1
  · filter_upwards [self_mem_nhdsWithin] with t h; exact (hs t h.1).2

/-- The right derivative suffices when its value is continuous. -/
theorem of_right (hf : ContinuousOn f (Ioi 0)) (hg : ContinuousOn g (Ioi 0))
    (hd : ∀ t, 0 < t → HasDerivWithinAt f (g t) (Ioi t) t) (hx : 0 < x) :
    HasDerivAt f (g x) x := by
  have hi := intervalIntegral.integral_hasDerivAt_right (f := g) (a := x) (b := x)
    (by simp) (hg.stronglyMeasurableAtFilter isOpen_Ioi x hx)
    (hg.continuousAt (isOpen_Ioi.mem_nhds hx))
  apply (hi.const_add (f x)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with t ht
  have hpos : 0 < min x t := lt_min hx ht
  have hs : uIcc x t ⊆ Ioi 0 := fun _ he => hpos.trans_le he.1
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right (hf.mono hs)
    (fun y hy => hd y (hpos.trans hy.1)) (hg.mono hs).intervalIntegrable]
  ring

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
end

section
/-! # Scalar extension of the finite polynomial row inequalities -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral

variable {K L : Type} [Field K] [Field L]

private theorem map_triple (φ : K →+* L) {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : X → Y → Z → K) (U : X → Y → Z → L) (he : ∀ x y z, φ (T x y z) = U x y z) :
    Tensor.map φ (Tensor.ofRaw (triple T)) = Tensor.ofRaw (triple U) := by
  rw [Tensor.map_ofRaw]
  refine Tensor.ofRaw_eq (Raw.equiv_coeff (fun _ => Equiv.refl _) fun x => ?_)
  erw [Raw.coeff_map, Raw.coeff_ofTable, Raw.coeff_ofTable]
  exact he _ _ _

theorem binary_of_closed (h : ∀ (L : Type) [Field L] [IsAlgClosed L], BinaryLaw L) : BinaryLaw K := by
  intro f hf p hp he m
  let L := AlgebraicClosure K
  let φ := algebraMap K L
  obtain ⟨g, hg, hmap⟩ := Tensor.extend_field L f hf
  have h₁ (a b : ℕ) : g (binary L a b) = f (binary K a b) := by
    rw [← hmap]
    exact congrArg g (map_triple φ _ _ (fun _ _ _ => by simp [convolution, apply_ite φ])).symm
  have h₂ (a b : ℕ) : g (reverseOutput L a b) = f (reverseOutput K a b) := by
    rw [← hmap]
    exact congrArg g (map_triple φ _ _ (fun _ _ _ => by simp [convolution, apply_ite φ])).symm
  rw [← hmap, Tensor.map_wire] at he
  simpa only [h₁, h₂] using h L g hg p hp he m

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-! # Coupled width curves at an actual finite placement -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Filter Minimum Spectral
open scoped Topology

theorem binary_law (K : Type) [Field K] : BinaryLaw K :=
  binary_of_closed (fun L _ _ => (closed_fulfills L).binary)

variable {K : Type} [Field K] {X : Type*} [PseudoMetricSpace X] (A : MatrixExponent.Prices.Atlas K X)
    (v : Fin 3 → X) {i j : Fin 3}

private theorem scaled_limit (hij : i ≠ j) {T : ℝ → Tensor K Site} (ht : ∀ n, T n ≠ 0)
    {B d : ℝ} (hd : 0 < d) (hD : 0 < A.price v 2)
    (h : Tendsto (fun n => Real.log 2 * A.price (placement v i j) (T n) -
      A.price v 2 * Real.log n) atTop (𝓝 B)) :
    Tendsto (fun n : ℝ => (point A (placement v i j) (T n) : ℝ) ^ (1 / (d / A.price v 2)) /
      n ^ (1 / (d / A.price v 2))) atTop (𝓝 (Real.exp (B / d))) := by
  apply ((h.div_const d).rexp).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  have hp := point_pos (point_mono A (placement v i j)) (ht n)
  rw [price_eq A (placement v i j), placement_two A v hij, Real.rpow_def_of_pos hp,
    Real.rpow_def_of_pos hn, ← Real.exp_sub]
  congr 1
  field_simp

theorem family [Infinite K] (u d : Vec) (hu : Positive u) (hd : Positive d)
    (hopp : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → Dist.dist (v j) (v k) = d i) :
    Family (pairs A v) d u (A.price v 2) := by
  refine ⟨pairs_symm A v, fun i j hij _ _ _ => pairs_scale A v hij, ?_⟩
  intro i j k hij hik hjk
  obtain ⟨hD, he⟩ := scaled_wire A v hij hik hjk (hd i) (hopp i j k hij hik hjk)
  let f := point A (placement v i j)
  let p := d i / A.price v 2
  have hp : 0 < p := div_pos (hd i) hD
  let a (n : ℝ) := ⌊u i * n⌋₊
  have ha : Tendsto (fun n => (a n : ℝ) / n) atTop (𝓝 (u i)) := tendsto_nat_floor_mul_div_atTop (hu i).le
  have hr (n : ℝ) := binary_law K f (point_mono _ _) p hp he (a n)
  apply curve_limit (q := fun n => n ^ (1 / p)) (hu i) ha (fun _ hn => by positivity) hr
    (fun _ _ => Real.exp_pos _)
  · intro x hx b hb
    exact scaled_limit A v hij (fun n => binary_ne_zero _ _) (hd i) hD
      (binary_limit A v hij (hu i) hx ha hb)
  · intro x hx b hb
    have h := binary_limit A v hik (hu i) hx ha hb
    simp_rw [price_turn A v hij hik hjk] at h
    exact scaled_limit A v hij (fun n => reverse_ne_zero _ _) (hd i) hD h

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# Radial contraction and the directional derivative

The energy `Q v s` is evaluated at reciprocal arm lengths `v` and
costs `s i / v i`. Increasing all costs by `t` adds `t • v` to `s`.
For a common cost the increment is explicit by log homogeneity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
open Minimum Set Filter

structure Radial (D : Vec → ℝ) (Q : Vec → Vec → ℝ) : Prop where
  continuous : ∀ v, Positive v → ContinuousOn (Q v) {s | Positive s}
  scale : ∀ v s, Positive v → Positive s → ∀ r : ℝ, 0 < r →
    Q v (r • s) = Q v s - D v⁻¹ * Real.log r
  contract : ∀ v w s, Positive v → Positive w → Positive s → v ≤ w → ∀ t : ℝ, 0 < t →
    Q w s - Q w (s + t • w) ≤ Q v s - Q v (s + t • v)

def potential (Q : Vec → Vec → ℝ) (v s : Vec) : ℝ :=
  Q v s + ∑ i, (v i)⁻¹ * Real.log (s i) - (∑ i, v i)⁻¹ * Real.log (∑ i, s i)

variable {F : Type} [Field F] {D : Vec → ℝ} {Q : Vec → Vec → ℝ} {v s : Vec}

private theorem pos_inv (h : Positive v) : Positive v⁻¹ := fun i => inv_pos.mpr (h i)
private theorem pos_sum (h : Positive v) : 0 < ∑ i, v i :=
  Finset.sum_pos (fun i _ => h i) Finset.univ_nonempty
private theorem pos_scale (h : Positive v) {r : ℝ} (hr : 0 < r) : Positive (r • v) :=
  fun i => mul_pos hr (h i)

theorem Radial.potential_scale (h : Radial D Q) (hv : Positive v) (hs : Positive s)
    {r : ℝ} (hr : 0 < r) :
    potential Q v (r • s) = potential Q v s - defect D v * Real.log r := by
  unfold potential defect
  rw [h.scale _ _ hv hs _ hr]
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, Real.log_mul hr.ne' (pos_sum hs).ne']
  simp_rw [Real.log_mul hr.ne' (hs _).ne', mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

theorem Radial.potential_continuous (h : Radial D Q) (hv : Positive v) :
    ContinuousOn (potential Q v) {s | Positive s} := by
  have hi (i : Fin 3) : ContinuousOn (fun s : Vec => Real.log (s i)) {s | Positive s} :=
    (continuous_apply i).continuousOn.log fun _ hs => (hs i).ne'
  have hs : ContinuousOn (fun s : Vec => Real.log (∑ i, s i)) {s | Positive s} :=
    (continuous_finsetSum _ (fun i _ => continuous_apply i)).continuousOn.log
      fun _ hs => (pos_sum hs).ne'
  exact ((h.continuous v hv).add (continuousOn_finsetSum _ (fun i _ =>
    (hi i).const_mul _))).sub (hs.const_mul _)

private theorem common_cost (h : Radial D Q) (hd : Tripod F D) (hs : Positive s)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    Q (r⁻¹ • s) s - Q (r⁻¹ • s) (s + t • (r⁻¹ • s)) =
      r * D s⁻¹ * Real.log (1 + t / r) := by
  have he : s + t • (r⁻¹ • s) = (1 + t / r) • s := by
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hi : (r⁻¹ • s)⁻¹ = r • s⁻¹ := by ext i; simp [mul_comm]
  rw [he, h.scale _ _ (pos_scale hs (inv_pos.mpr hr)) hs _ (by positivity), hi,
    hd.scale _ (pos_inv hs) r hr]
  ring

private theorem radii (hv : Positive v) (hs : Positive s) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ v ≤ a⁻¹ • s ∧ b⁻¹ • s ≤ v := by
  let x := ∑ i, v i / s i
  let y := ∑ i, s i / v i
  have hx : 0 < x := Finset.sum_pos (fun i _ => div_pos (hv i) (hs i)) Finset.univ_nonempty
  have hy : 0 < y := Finset.sum_pos (fun i _ => div_pos (hs i) (hv i)) Finset.univ_nonempty
  refine ⟨x⁻¹, y, by positivity, hy, ?_, ?_⟩
  · rw [inv_inv]
    intro i
    exact (div_le_iff₀ (hs i)).mp (Finset.single_le_sum
      (fun j _ => (div_pos (hv j) (hs j)).le) (Finset.mem_univ i))
  · intro i
    have he : s i / v i ≤ y := Finset.single_le_sum
      (fun j _ => (div_pos (hs j) (hv j)).le) (Finset.mem_univ i)
    exact (inv_mul_le_iff₀ hy).2 ((div_le_iff₀ (hv i)).mp he)

private theorem Radial.right (h : Radial D Q) (hd : Tripod F D) (hv : Positive v)
    {p : ℝ → Vec} {x : ℝ} (hs : Positive (p x))
    (hp : ∀ t : ℝ, p (x + t) = p x + t • v) :
    HasDerivWithinAt (fun t => Q v (p t)) (-D (p x)⁻¹) (Ioi x) x := by
  obtain ⟨a, b, ha, hb, ha', hb'⟩ := radii hv hs
  apply right_derivative ha hb
  intro t ht
  rw [hp t, ← common_cost h hd hs ha ht, ← common_cost h hd hs hb ht]
  exact ⟨h.contract _ _ _ hv (pos_scale hs (by positivity)) hs ha' t ht,
    h.contract _ _ _ (pos_scale hs (by positivity)) hv hs hb' t ht⟩

theorem Radial.direction (h : Radial D Q) (hd : Tripod F D) (hv : Positive v)
    {u : Vec} {t : ℝ} (hp : Positive (u + t • v)) :
    HasDerivWithinAt (fun s => potential Q v (u + s • v))
      (-defect D (u + t • v)) (Ioi t) t := by
  let p (s : ℝ) := u + s • v
  have he := h.right hd hv (p := p) hp (by intro x; unfold p; rw [add_smul, add_assoc])
  have h₁ (i : Fin 3) : HasDerivAt (fun s => p s i) (v i) t := by
    simpa only [p, Pi.add_apply, Pi.smul_apply, smul_eq_mul, id_eq, one_mul] using!
      ((hasDerivAt_id t).mul_const (v i)).const_add (u i)
  have h₂ (i : Fin 3) :
      HasDerivAt (fun s => (v i)⁻¹ * Real.log (p s i)) (p t i)⁻¹ t := by
    have he : (v i)⁻¹ * (v i / p t i) = (p t i)⁻¹ := by
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (hv i).ne', one_mul]
    rw [← he]
    exact ((h₁ i).log (hp i).ne').const_mul _
  have h₃ : HasDerivAt (fun s => ∑ i, p s i) (∑ i, v i) t :=
    HasDerivAt.fun_sum fun i _ => h₁ i
  have h₄ : HasDerivAt (fun s => (∑ i, v i)⁻¹ * Real.log (∑ i, p s i)) (∑ i, p t i)⁻¹ t := by
    have he : (∑ i, v i)⁻¹ * ((∑ i, v i) / ∑ i, p t i) = (∑ i, p t i)⁻¹ := by
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (pos_sum hv).ne', one_mul]
    rw [← he]
    exact (h₃.log (pos_sum hp).ne').const_mul _
  have h₅ : HasDerivAt (fun s => ∑ i, (v i)⁻¹ * Real.log (p s i)) (∑ i, (p t i)⁻¹) t :=
    HasDerivAt.fun_sum fun i _ => h₂ i
  rw [show -defect D (u + t • v) = -D (p t)⁻¹ + (∑ i, (p t i)⁻¹) - (∑ i, p t i)⁻¹ by
    unfold defect p; ring]
  exact (he.add h₅.hasDerivWithinAt).sub h₄.hasDerivWithinAt

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
end

/-! # Integrating the energy along a ray from a coordinate axis -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
open Minimum Set Filter
open scoped Topology

def unit (i : Fin 3) : Vec := fun j => if j = i then 1 else 0

theorem unit_move (v : Vec) (i : Fin 3) : unit i + v = move v i 1 := by
  ext j; by_cases h : j = i <;> simp [unit, move, h, add_comm]

def along (Q : Vec → Vec → ℝ) (v : Vec) (i : Fin 3) (t : ℝ) : ℝ :=
  potential Q v (unit i + t • v)

variable {F : Type} [Field F] {D : Vec → ℝ} {Q : Vec → Vec → ℝ} {v u : Vec} {s t : ℝ}

theorem pos_along (hv : Positive v) (i : Fin 3) (ht : 0 < t) :
    Positive (unit i + t • v) := by
  rw [unit_move]
  exact (show Positive (t • v) from fun j => mul_pos ht (hv j)).move i zero_le_one

theorem Radial.axis_deriv (h : Radial D Q) (hd : Tripod F D) (hv : Positive v) (i : Fin 3)
    (ht : 0 < t) : HasDerivAt (along Q v i) (-defect D (move (t • v) i 1)) t := by
  have hp : ContinuousOn (along Q v i) (Ioi 0) :=
    (h.potential_continuous hv).comp (by fun_prop) (fun _ hx => pos_along hv i hx)
  let f (x : ℝ) := -defect D (move (x • v) i 1)
  have hc : ContinuousOn f (Ioi 0) := by
    have he : ContinuousOn (fun x : ℝ => 1 / x) (Ioi 0) :=
      continuousOn_const.div continuousOn_id (fun _ hx => ne_of_gt hx)
    have h₁ := (hd.regular.continuous _ hv i).comp he (fun x hx => mem_Ici.mpr (one_div_pos.mpr (show 0 < x from hx)).le)
    refine ((h₁.div continuousOn_id (fun _ hx => ne_of_gt hx)).neg).congr ?_
    intro x hx
    exact congrArg Neg.neg (hd.regular.scale hv i hx zero_le_one)
  refine of_right hp hc ?_ ht
  intro x hx
  unfold f
  rw [← unit_move]
  exact h.direction hd hv (pos_along hv i hx)

theorem Radial.axis_far (h : Radial D Q) (hv : Positive v) (i j : Fin 3) :
    Tendsto (fun T : ℝ => along Q v i T - along Q v j T) atTop (𝓝 0) := by
  let p (i : Fin 3) (T : ℝ) := T⁻¹ • unit i + v
  have hpos i T (ht : 0 < T) : Positive (p i T) := by
    intro j
    have := hv j
    unfold p unit
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split <;> positivity
  have he i T (ht : 0 < T) : along Q v i T = potential Q v (p i T) - defect D v * Real.log T := by
    unfold along
    rw [show unit i + T • v = T • p i T by simp [p, smul_add, ht.ne']]
    exact h.potential_scale hv (hpos _ _ ht) ht
  have hl (i : Fin 3) : Tendsto (fun T => potential Q v (p i T)) atTop (𝓝 (potential Q v v)) := by
    apply ((h.potential_continuous hv) v hv).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, (eventually_gt_atTop 0).mono (fun T hT => hpos _ _ hT)⟩
    simpa [p] using ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).smul_const (unit i)).add_const v
  have hh := (hl i).sub (hl j)
  rw [sub_self] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with T ht
  rw [he _ _ ht, he _ _ ht]
  ring

/-- A segment starting near an axis has rate derivative of absolute value
at most one by the star bound, uniformly in its distance to that axis. -/
theorem Radial.segment (h : Radial D Q) (hd : StarTripod F D) (hv : Positive v)
    (hu : Positive u) (hs : 1 ≤ ∑ i, u i) (ht : 0 ≤ t) :
    |potential Q v (u + t • v) - potential Q v u| ≤ t := by
  let p (x : ℝ) := u + x • v
  have hu' (x) (hx : 0 ≤ x) : u ≤ p x :=
    fun i => le_add_of_nonneg_right (mul_nonneg hx (hv i).le)
  have hp x (hx : 0 ≤ x) : Positive (p x) := fun i => (hu i).trans_le (hu' x hx i)
  have hc : ContinuousOn (fun x => potential Q v (p x)) (Icc 0 t) :=
    (h.potential_continuous hv).comp (by unfold p; fun_prop) (fun _ hx => hp _ hx.1)
  have hb (x : ℝ) (hx : x ∈ Ico 0 t) : ‖-defect D (p x)‖ ≤ 1 := by
    rw [norm_neg, Real.norm_of_nonneg (hd.toTripod.regular.nonneg _ (hp _ hx.1))]
    refine (hd.cap (hp _ hx.1)).trans (inv_le_one_of_one_le₀ ?_)
    exact hs.trans (Finset.sum_le_sum (fun i _ => hu' x hx.1 i))
  have he := norm_image_sub_le_of_norm_deriv_right_le_segment hc
    (fun _ hx => (h.direction hd.toTripod hv (hp _ hx.1)).Ici_of_Ioi) hb t ⟨ht, le_rfl⟩
  simpa only [p, zero_smul, add_zero, Real.norm_eq_abs, sub_zero, one_mul] using he

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
end

/-! # Directional comparison from energy and the axis limits -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
open Minimum Set Filter
open scoped Topology

def near (i : Fin 3) (r : ℝ) : Vec := fun j => if j = i then 1 else r

private theorem near_pos (i : Fin 3) {r : ℝ} (hr : 0 < r) : Positive (near i r) := by
  intro j
  unfold near
  split <;> positivity

private theorem near_sum (i : Fin 3) {r : ℝ} (hr : 0 < r) : 1 ≤ ∑ j, near i r j := by
  have he := Finset.single_le_sum (fun j _ => (near_pos i hr j).le) (Finset.mem_univ i)
  simpa [near] using he

private theorem near_limit (i : Fin 3) : Tendsto (near i) (𝓝[>] 0) (𝓝 (unit i)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases h : j = i
  · simp [near, unit, h]
  · simpa only [near, unit, ite_eq_right h] using!
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0))

variable {F : Type} [Field F] {D : Vec → ℝ} {Q : Vec → Vec → ℝ} {v : Vec}

private theorem Radial.axis_near (h : Radial D Q) (hd : StarTripod F D)
    (hv : Positive v) {i : Fin 3} {b : ℝ}
    (hb : Tendsto (fun r => potential Q v (near i r)) (𝓝[>] 0) (𝓝 b)) :
    Tendsto (fun T : ℝ => along Q v i (1 / T)) atTop (𝓝 b) := by
  have he (t : ℝ) (ht : 0 < t) : |along Q v i t - b| ≤ t := by
    have hu : Tendsto (fun r => potential Q v (near i r + t • v)) (𝓝[>] 0)
        (𝓝 (along Q v i t)) := by
      apply ((h.potential_continuous hv) _ (pos_along hv i ht)).tendsto.comp
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(near_limit i).add_const _, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with r hr j
      exact add_pos (near_pos i hr j) (mul_pos ht (hv j))
    apply le_of_tendsto (hu.sub hb).abs
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact h.segment hd hv (near_pos i hr) (near_sum i hr) ht.le
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_gt_atTop (1 / ε)] with T hT
  rw [Real.dist_eq]
  have hT₀ := (one_div_pos.mpr hε).trans hT
  exact (he _ (one_div_pos.mpr hT₀)).trans_lt ((one_div_lt hT₀ hε).mpr hT)

/-- Axis limits of the corrected energy agree to the accuracy of
the diagonal defect, with local control up to the open face. -/
def AxisLimits (D : Vec → ℝ) (Q : Vec → Vec → ℝ) : Prop :=
  ∀ v, Positive v → ∃ E : ℝ, 0 ≤ E ∧ ∀ w, Positive w → w ≤ (2 : ℝ) • v →
    v 1 ≤ w 1 → v 2 ≤ w 2 → ∃ b : Fin 3 → ℝ,
      (∀ i, Tendsto (fun r => potential Q w (near i r)) (𝓝[>] 0) (𝓝 (b i))) ∧
      ∀ i j, b i - b j ≤ E * defect D w

theorem Radial.uniform (h : Radial D Q) (hd : StarTripod F D) (ha : AxisLimits D Q) :
    Face.Uniform (defect D) := by
  intro v hv
  obtain ⟨E, hE, hb⟩ := ha v hv
  refine ⟨E, hE, ?_⟩
  intro w hw hu h₁ h₂ i j ζ hζ
  obtain ⟨b, hl, he⟩ := hb w hw hu h₁ h₂
  have ht := ((h.axis_near hd hw (hl i)).sub (h.axis_near hd hw (hl j))).sub
    (h.axis_far hw i j)
  rw [sub_zero] at ht
  have hs := (he i j).trans_lt (lt_add_of_pos_right _ hζ)
  filter_upwards [eventually_ge_atTop (1 : ℝ), ht.eventually_lt_const hs] with T hT hh
  have hm (k : Fin 3) := integral_potential hd.toTripod.regular hw
    (fun x hx => h.axis_deriv hd.toTripod hw k hx) hT
  rw [hm i, hm j]
  linarith

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
end

/-! # Degree costs and log-homogeneous variational energies -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
open Minimum Profile Set

variable {p d x s : ℝ}

theorem log_max (hp : 0 < p) (hs : 0 < s) (hx : 0 < x) :
    p * Real.log x - s * x ≤ p * Real.log (p / s) - p := by
  have h := Real.log_le_sub_one_of_pos (div_pos (mul_pos hs hx) hp)
  rw [Real.log_div (by positivity) hp.ne', Real.log_mul hs.ne' hx.ne'] at h
  have hh := mul_le_mul_of_nonneg_left h hp.le
  rw [mul_sub p (s * x / p), mul_div_cancel₀ _ hp.ne'] at hh
  rw [Real.log_div hp.ne' hs.ne']
  linarith only [hh]

def cost {ι : Type} [Fintype ι] (s x : ι → ℝ) := ∑ i, s i * x i

def variational {ι : Type} [Fintype ι] (R : (ι → ℝ) → ℝ) (d : ℝ) (s : ι → ℝ) : ℝ :=
  sSup ((fun x => d + R x - cost s x) '' {x | ∀ i, 0 < x i})

structure Growth (R : Vec → ℝ) (d : ℝ) : Prop where
  pos : 0 < d
  scale : ∀ x, Positive x → ∀ t : ℝ, 0 < t → R (t • x) = R x + d * Real.log t
  bound : ∀ x, Positive x → R x ≤ d * Real.log (mass x)

variable {R : Vec → ℝ} {v w u : Vec} {t : ℝ}

theorem variational_le {s : Vec} {B : ℝ} (h : ∀ x, Positive x → d + R x - cost s x ≤ B) :
    variational R d s ≤ B := by
  apply csSup_le
  · exact ⟨_, fun _ => 1, fun _ => zero_lt_one, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx

theorem Growth.lower (h : Growth R d) (hv : Positive v) (hw : Positive w) :
    d + R w - cost v w ≤ variational R d v := by
  refine le_csSup ?_ ⟨w, hw, rfl⟩
  let p := min (v 0) (min (v 1) (v 2))
  have hp : 0 < p := lt_min (hv _) (lt_min (hv _) (hv _))
  have hv' (i : Fin 3) : p ≤ v i := by fin_cases i <;> simp [p]
  refine ⟨d * Real.log (d / p), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hc : p * mass x ≤ cost v x := by
    rw [cost, mass, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hv' i) (hx i).le)
  linarith only [hc, h.bound _ hx, log_max h.pos hp (mass_pos hx)]

private theorem cost_scale (s x : Vec) (t : ℝ) : cost (t • s) x = cost s (t • x) := by
  unfold cost
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem Growth.log_scale (h : Growth R d) (hv : Positive v) (ht : 0 < t) :
    variational R d (t • v) = variational R d v - d * Real.log t := by
  have upper {v : Vec} {t : ℝ} (hv : Positive v) (ht : 0 < t) :
      variational R d (t • v) ≤ variational R d v - d * Real.log t := by
    apply variational_le
    intro x hx
    have he := h.lower hv (show Positive (t • x) from fun i => mul_pos ht (hx i))
    rw [h.scale x hx _ ht, ← cost_scale] at he
    linarith
  refine le_antisymm (upper hv ht) ?_
  have he := upper (show Positive (t • v) from fun i => mul_pos ht (hv i)) (inv_pos.mpr ht)
  rw [inv_smul_smul₀ ht.ne', Real.log_inv] at he
  linarith

private theorem open_positive : IsOpen {v : Vec | Positive v} := by
  simp only [Positive, Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

theorem Growth.continuous (h : Growth R d) :
    ContinuousOn (variational R d) {v | Positive v} := by
  apply ConvexOn.continuousOn open_positive
  constructor
  · intro v hv w hw a b ha hb hab i
    change 0 < a * v i + b * w i
    rcases eq_or_lt_of_le ha with rfl | ha
    · simpa [show b = 1 by linarith] using hw i
    exact add_pos_of_pos_of_nonneg (mul_pos ha (hv i)) (mul_nonneg hb (hw i).le)
  intro v hv w hw a b ha hb hab
  apply variational_le
  intro x hx
  have he : cost (a • v + b • w) x = a * cost v x + b * cost w x := by
    simp only [cost, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hh : (a + b) * (d + R x) = d + R x := by rw [hab, one_mul]
  rw [he, smul_eq_mul, smul_eq_mul]
  linarith only [mul_le_mul_of_nonneg_left (h.lower hv hx) ha,
    mul_le_mul_of_nonneg_left (h.lower hw hx) hb, hh]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
end

/-! # Profiles at the origin and the terminals of a tripod -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
open Minimum Profile

/-- At reciprocal lengths `v`, `R` is the three-input profile with
output at the origin. `P i j` has inputs `i,j` and the third terminal
as output. -/
structure Root (D : Vec → ℝ) (v : Vec) (R : Vec → ℝ) (P : PairPrices) : Prop where
  growth : Growth R (D v⁻¹)
  family : Family P (opposite v) (criticalWidth v) (D v⁻¹)
  chord : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ x, Positive x →
    opposite v i * R x ≤ (v j)⁻¹ * P i j (x i) (x j) + (v k)⁻¹ * P i k (x i) (x k)
  pairing : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ x, Positive x → x k = x i + x j →
    P i j (x i) (x j) ≤ R x

/-- Costs and arm lengths are both rescaled by `1/v i`. -/
def adjusted (D : Vec → ℝ) (R : Vec → Vec → ℝ) (v s : Vec) :=
  variational (R v⁻¹) (D v⁻¹) (s / v)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
end

/-! # Locally uniform axis agreement on a homogeneous spectral tripod -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Minimum Filter
open scoped Topology

variable {F : Type} [Field F] {D : Vec → ℝ} {v : Vec} {P : PairPrices}

def axisValue (D : Vec → ℝ) (v : Vec) (P : PairPrices) (i : Fin 3) : ℝ :=
  intercept P (opposite v) (criticalWidth v) i +
    residual D v i * Real.log (residual D v i / ((v i)⁻¹ * criticalWidth v i))

theorem Family.at_critical (h : Family P (opposite v) (criticalWidth v) (D v⁻¹))
    (hd : StarTripod F D) (hv : Positive v) :
    Critical (criticalWidth v) (intercept P (opposite v) (criticalWidth v)) (opposite v)
      (fun i j => P i j (criticalWidth v i) (criticalWidth v j)) (defect D v) :=
  h.critical (critical_pos hv) (opposite_pos hv) (hd.pos _ (fun i => inv_pos.mpr (hv i))).le
    (fun _ _ _ => critical_sum hv) (fun _ _ => critical_pair D hv)

private theorem correction {a u b Δ ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hu : ε ≤ u)
    (hΔ : 0 ≤ Δ) (hb : b = a * u + Δ) (hb' : b ≤ a) :
    0 ≤ b * Real.log (b / (a * u)) ∧ b * Real.log (b / (a * u)) ≤ Δ / ε := by
  have hu' := hε.trans_le hu
  have hb₀ : 0 < b := by rw [hb]; positivity
  have hh := (one_le_div (mul_pos ha hu')).mpr (show a * u ≤ b by linarith)
  have hl := Real.log_nonneg hh
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ a * Real.log (b / (a * u)) := mul_le_mul_of_nonneg_right hb' hl
    _ ≤ a * (b / (a * u) - 1) := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by positivity)) ha.le
    _ = Δ / u := by rw [hb]; field_simp; ring
    _ ≤ Δ / ε := div_le_div_of_nonneg_left hΔ hε hu

/-- The intercept differences cost at most a constant times the
absolute defect, even when an arm length tends to infinity. -/
theorem Family.axis_bound (h : Family P (opposite v) (criticalWidth v) (D v⁻¹))
    (hd : StarTripod F D) (hv : Positive v) {ε : ℝ} (hε : 0 < ε)
    (hu : ∀ i, ε ≤ criticalWidth v i) (i j : Fin 3) :
    axisValue D v P i - axisValue D v P j ≤ (5 / ε ^ 2 + 1 / ε) * defect D v := by
  have hz := hd.toTripod.regular.nonneg _ hv
  have he := (h.at_critical hd hv).intercepts (opposite_pos hv) hz hε hu (critical_le hv) i j
  have hh (i) := correction (inv_pos.mpr (hv i)) hε (hu i) hz (residual_eq D hv i)
    (residual_bounds hd hv i).2
  have hi := (hh i).2
  have hj := (hh j).1
  unfold axisValue
  simp only [div_eq_mul_inv] at hi hj he ⊢
  linarith only [hi, hj, he]

theorem axisLimits {Q : Vec → Vec → ℝ} (hd : StarTripod F D)
    (h : ∀ v, Positive v → ∃ P : PairPrices, Family P (opposite v) (criticalWidth v) (D v⁻¹) ∧
      ∀ i, Tendsto (fun r => Energy.potential Q v (Energy.near i r)) (𝓝[>] 0)
        (𝓝 (axisValue D v P i))) :
    Energy.AxisLimits D Q := by
  intro v hv
  obtain ⟨ε, hε, he⟩ := uniform_width hv
  refine ⟨5 / ε ^ 2 + 1 / ε, by positivity, ?_⟩
  intro w hw hw' h₁ h₂
  obtain ⟨P, hp, hlim⟩ := h w hw
  exact ⟨axisValue D w P, hlim, hp.axis_bound hd hw hε (he _ hw hw' h₁ h₂)⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-! # The polynomial profile at the origin of a tripod -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral Minimum Filter
open scoped Topology

variable {F : Type} [Field F] (A : MatrixExponent.Prices.Atlas F Twig) {a v x : Vec} {i j k : Fin 3}

def rootPlacement (a : Vec) : Option (Fin 3) → Twig := Multi.sites Twig.origin (Twig.mark a)

def rootPrices (a x : Vec) : ℝ :=
  Twig.label A a * Real.log (profile (point A (rootPlacement a)) x)

/-- Only the output moves along the geodesic through the origin. -/
private theorem root_chord (ha : Positive a) (hjk : j ≠ k) (T : Tensor F (Option (Fin 3))) :
    (a j + a k) * A.price (rootPlacement a) T ≤
      a j * A.price (Twig.mark a ∘ terminal k) T + a k * A.price (Twig.mark a ∘ terminal j) T := by
  let t := a k / (a j + a k)
  have hd := add_pos (ha j) (ha k)
  have ht : 0 ≤ t := (div_pos (ha k) hd).le
  have ht' : t ≤ 1 := (div_le_one hd).mpr (by linarith [ha j])
  have hk : t * (a j + a k) = a k := div_mul_cancel₀ _ hd.ne'
  have hj : (1 - t) * (a j + a k) = a j := by linarith
  let f l := Twig.mark a ∘ terminal l
  have hm (l) : Dist.dist Twig.origin (Twig.mark a l) = a l := by
    simp [Twig.mark, Twig.radius, (ha l).le]
  have hdist : Dist.dist (Twig.mark a k) (Twig.mark a j) = a j + a k := by
    rw [Twig.mark_dist ha ha, ite_eq_right hjk.symm, add_comm]
  have h₁ (s) : Dist.dist (f k s) (rootPlacement a s) = t * Dist.dist (f k s) (f j s) := by
    cases s with
    | some l => simp [f, terminal, rootPlacement, Multi.sites]
    | none =>
      change Dist.dist (Twig.mark a k) Twig.origin = t * Dist.dist (Twig.mark a k) (Twig.mark a j)
      rw [dist_comm, hm, hdist, hk]
  have h₂ (s) : Dist.dist (rootPlacement a s) (f j s) = (1 - t) * Dist.dist (f k s) (f j s) := by
    cases s with
    | some l => simp [f, terminal, rootPlacement, Multi.sites]
    | none =>
      change Dist.dist Twig.origin (Twig.mark a j) = (1 - t) * Dist.dist (Twig.mark a k) (Twig.mark a j)
      rw [hm, hdist, hj]
  have h := mul_le_mul_of_nonneg_left (A.chord ht ht' h₁ h₂ T) hd.le
  rwa [mul_add, ← mul_assoc, ← mul_assoc, mul_comm (a j + a k) (1 - t), hj, mul_comm (a j + a k) t, hk] at h

theorem root_label (ha : Positive a) : A.price (rootPlacement a) 2 = Twig.label A a := by
  have he (l : Fin 3) : A.price (Twig.mark a ∘ terminal l) 2 = Twig.label A a := by
    have hs : Function.Surjective (terminal l) := fun m => ⟨some m, rfl⟩
    rw [A.place, Function.comp_apply, Tensor.place_eq_group _ hs, map_ofNat]
    rfl
  apply le_antisymm
  · have h := root_chord A ha (j := 0) (k := 1) (by decide) 2
    rw [he, he, ← add_mul] at h
    exact le_of_mul_le_mul_left h (add_pos (ha 0) (ha 1))
  · change A.price (rootPlacement a ∘ some) 2 ≤ _
    rw [A.place, Function.comp_apply]
    apply Multi.monotone_price
    have h := Tensor.place_add_le (K := F) (some : Fin 3 → Option (Fin 3)) 1 1
    simp only [Tensor.place_one, one_add_one_eq_two] at h
    exact h

variable [Infinite F]

theorem root_limit (ha : Positive a) (hx : Positive x)
    {α : Type*} {l : Filter α} {N : α → ℝ} (hN : Tendsto N l atTop) {L : α → Fin 3 → ℕ}
    (hL : ∀ i, Tendsto (fun n => (L n i : ℝ) / N n) l (𝓝 (x i))) :
    Tendsto (fun n => Real.log 2 * A.price (rootPlacement a) (polynomial F (L n)) -
      Twig.label A a * Real.log (N n)) l (𝓝 (rootPrices A a x)) := by
  have h := (log_profile_limit (point_mono A (rootPlacement a)) hx hN hL).const_mul (Twig.label A a)
  apply h.congr'
  filter_upwards [] with n
  rw [price_eq A (rootPlacement a), root_label A ha, mul_sub]

theorem root_growth (hA : Twig.Homogeneous A) (ha : Positive a) :
    Energy.Growth (rootPrices A a) (Twig.label A a) := by
  let f := point A (rootPlacement a)
  have hf : Monotone f := point_mono A _
  have hp := hA.star.pos a ha
  refine ⟨hp, ?_, ?_⟩
  · intro x hx s hs
    have he : profile f (s • x) = s * profile f x := (scaling_polynomial f hf).scale_smul hx hs
    unfold rootPrices
    rw [he, Real.log_mul hs.ne' (profile_pos hf hx).ne']
    ring
  · intro x hx
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (profile_pos hf hx)
      ((scaling_polynomial f hf).scale_bound hx)) hp.le

private def floors (x : Vec) (N : ℝ) (i : Fin 3) := ⌊x i * N⌋₊

private theorem floor_lim (hx : Positive x) (i : Fin 3) :
    Tendsto (fun N : ℝ => (floors x N i : ℝ) / N) atTop (𝓝 (x i)) :=
  tendsto_nat_floor_mul_div_atTop (hx i).le

private theorem floors_pos (hx : Positive x) (i : Fin 3) :
    ∀ᶠ N : ℝ in atTop, 0 < floors x N i := by
  filter_upwards [eventually_ge_atTop (1 / x i)] with N hN
  exact Nat.floor_pos.mpr (by rw [mul_comm]; exact (div_le_iff₀ (hx i)).mp hN)

private theorem pair_lim (a : Vec) (hx : Positive x) (hij : i ≠ j) :
    Tendsto (fun N : ℝ =>
      Real.log 2 * A.price (placement (Twig.mark a) i j)
        (polynomial F (two (floors x N i) (floors x N j))) - Twig.label A a * Real.log N)
      atTop (𝓝 (pairs A (Twig.mark a) i j (x i) (x j))) := by
  apply pairs_limit A (Twig.mark a) hij (hx i) (hx j) tendsto_id
  rintro (_ | _) <;> exact floor_lim hx _

theorem profile_pairing (ha : Positive a) (hx : Positive x)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hk : x k = x i + x j) :
    pairs A (Twig.mark a) i j (x i) (x j) ≤ rootPrices A a x := by
  refine le_of_tendsto_of_tendsto (pair_lim A a hx hij)
    (root_limit A ha hx tendsto_id (floor_lim hx)) ?_
  filter_upwards [floors_pos hx i, eventually_ge_atTop 0] with N h₁ hN
  have h₂ : floors x N i + floors x N j ≤ floors x N k := by
    unfold floors
    rw [hk, add_mul]
    apply Nat.le_floor
    rw [Nat.cast_add]
    exact add_le_add (Nat.floor_le (mul_nonneg (hx i).le hN)) (Nat.floor_le (mul_nonneg (hx j).le hN))
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [show placement (Twig.mark a) i j = rootPlacement a ∘ (some ∘ pairSite i j) from rfl,
    A.place, Function.comp_apply]
  exact Multi.monotone_price A _ (extract_pair hij hik hjk h₁ h₂)

theorem profile_chord (ha : Positive a) (hx : Positive x)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (a j + a k) * rootPrices A a x ≤
      a j * pairs A (Twig.mark a) i j (x i) (x j) + a k * pairs A (Twig.mark a) i k (x i) (x k) := by
  refine le_of_tendsto_of_tendsto
    ((root_limit A ha hx tendsto_id (floor_lim hx)).const_mul (a j + a k))
    (((pair_lim A a hx hij).const_mul (a j)).add ((pair_lim A a hx hik).const_mul (a k))) ?_
  filter_upwards [floors_pos hx i] with N h₁
  let T := polynomial F (floors x N)
  have hbound {j k} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      A.price (Twig.mark a ∘ terminal k) T ≤ A.price (placement (Twig.mark a) i j)
        (polynomial F (two (floors x N i) (floors x N j))) := by
    rw [placement, A.place, A.place]
    exact Multi.monotone_price A _ (absorb hij hik hjk h₁)
  have h := (root_chord A ha hjk T).trans
    (add_le_add (mul_le_mul_of_nonneg_left (hbound hij hik hjk) (ha j).le)
      (mul_le_mul_of_nonneg_left (hbound hik hij hjk.symm) (ha k).le))
  have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ Real.log 2 by positivity)
  dsimp only [id_eq, T] at h' ⊢
  linarith only [h']

theorem root (hA : Twig.Homogeneous A) (hv : Positive v)
    (hf : Family (pairs A (Twig.mark v⁻¹)) (opposite v) (criticalWidth v) (Twig.label A v⁻¹)) :
    Energy.Root (Twig.label A) v (rootPrices A v⁻¹) (pairs A (Twig.mark v⁻¹)) := by
  have ha : Positive v⁻¹ := fun i => inv_pos.mpr (hv i)
  refine ⟨root_growth A hA ha, hf, ?_, ?_⟩
  · intro i j k hij hik hjk x hx
    rw [opposite_eq v hij hik hjk]
    exact profile_chord A ha hx hij hik hjk
  · intro i j k hij hik hjk x hx hk
    exact profile_pairing A ha hx hij hik hjk hk

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end
