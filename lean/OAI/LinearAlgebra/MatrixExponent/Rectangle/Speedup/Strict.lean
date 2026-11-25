import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Price
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup.Dense
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Dual
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup.Directions
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Monotone
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Surplus

universe u

section
/-! # Supporting lines to the gain from a group -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup

private theorem remainder_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (t : ℝ) :
    Real.exp (a * t) - 1 - a * t ≤ Real.exp (b * t) - 1 - b * t := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((b - a) * t)) (Real.exp_pos (a * t)).le
  rw [← Real.exp_add, show a * t + (b - a) * t = b * t by ring] at h
  have hh : 0 ≤ (Real.exp (a * t) - 1) * ((b - a) * t) := by
    rcases le_total 0 t with ht | ht
    · exact mul_nonneg (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg ha ht)))
        (mul_nonneg (sub_nonneg.mpr hab) ht)
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ha ht)))
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab) ht)
  linarith only [h, hh]

theorem gain_tangent {d b x : ℝ} (hd : 1 ≤ d) (hdb : d ≤ b) (hx : 0 ≤ x) :
    ∃ t : ℝ, 0 ≤ t ∧ ∀ y : ℝ, b ^ x - d ^ x + t * (y - x) ≤ b ^ y - d ^ y := by
  have hd₀ := zero_lt_one.trans_le hd
  have hb₀ := hd₀.trans_le hdb
  have ha := Real.log_nonneg hd
  have hab := Real.log_le_log hd₀ hdb
  have hpow := Real.rpow_le_rpow hd₀.le hdb hx
  refine ⟨b ^ x * Real.log b - d ^ x * Real.log d, sub_nonneg.mpr
    (mul_le_mul hpow hab ha (by positivity)), ?_⟩
  intro y
  have h := remainder_mono ha hab (y - x)
  have h₀ : 0 ≤ Real.exp (Real.log d * (y - x)) - 1 - Real.log d * (y - x) := by
    linarith only [Real.add_one_le_exp (Real.log d * (y - x))]
  have he := mul_le_mul hpow h h₀ (by positivity)
  have hr (a : ℝ) (ha : 0 < a) : a ^ x * Real.exp (Real.log a * (y - x)) = a ^ y := by
    rw [← Real.rpow_def_of_pos ha, ← Real.rpow_add ha, add_sub_cancel]
  linarith only [he, hr d hd₀, hr b hb₀]

theorem log_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x + x * (Real.log y - Real.log x) ≤ y := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hy hx)) hx.le
  rw [Real.log_div hy.ne' hx.ne', mul_sub x (y / x), mul_div_cancel₀ _ hx.ne'] at h
  linarith

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup
end

/-!
# Grouped speedup for spectral points

Apply pole cancellation on the dense locus of spanning pivots, then
extend the price inequality to arbitrary decompositions. Subadditivity
lets us treat each full group independently.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Spectral Speedup

namespace Speedup

variable {K : Type} [Field K] [Infinite K] {X : Leg → Type} [∀ s, Fintype (X s)]
    {d m : ℕ} {a b : Leg} {f : Tensor K Leg →+* NNReal}

private theorem one_group (P : Family K X d) (A : Family K X m) (hm : 0 < m)
    (hd : ∀ s, Fintype.card (X s) ≤ d) (hf : Monotone f) (hab : a ≠ b) :
    (f (table (form P + form A)) : ℝ) ≤
      (d : ℝ) + m + f (Tensor.wire K a b d) - f (Tensor.wire K a b m) := by
  have hw : (f (Tensor.wire K a b m) : ℝ) ≤ m := by
    have h := hf (Tensor.le_term_count (Raw.wire K a b m))
    change f (Tensor.wire K a b m) ≤ f (Fintype.card (Fin m) : Tensor K Leg) at h
    rw [Fintype.card_fin, map_natCast] at h
    exact_mod_cast h
  apply (spanning_dense P A hd).price f hf
    (by linarith [show 0 ≤ (f (Tensor.wire K a b d) : ℝ) by positivity])
  rintro _ ⟨B, hB, rfl⟩
  let M := (d : Tensor K Leg) + (m : Tensor K Leg) + Tensor.wire K a b d
  have hpath := degeneration (extend m B) (extend m A) (extra X a b m)
    hm hab hB.extend (extra_const a b)
  have h := hpath.price f hf (B := (f M : ℝ)) (by positivity)
    (fun _ hx => NNReal.coe_le_coe.mpr (hf hx))
  change (f (table _) : ℝ) ≤ _ at h
  rw [table_extra] at h
  unfold M at h
  rw [map_add, map_add, map_add, map_natCast, map_natCast] at h
  exact le_sub_iff_add_le.mpr h

omit [Infinite K] [∀ s, Fintype (X s)] in
private theorem split_form (A : Family K X (d + m)) :
    ∃ P : Family K X d, ∃ B : Family K X m, form A = form P + form B := by
  exact ⟨fun l => A (Fin.castAdd m l), fun l => A (Fin.natAdd d l),
    funext fun _ => Fin.sum_univ_add _⟩

theorem groups (hf : Monotone f) (hab : a ≠ b) (hd : ∀ s, Fintype.card (X s) ≤ d) (hm : 0 < m)
    (h : ℕ) {r : ℕ} (hr : (d + m) * h ≤ r) (A : Family K X r) :
    (f (table (form A)) : ℝ) + h * ((f (Tensor.wire K a b m) : ℝ) - f (Tensor.wire K a b d)) ≤ r := by
  induction h generalizing r with
  | zero =>
    have h := hf (form_le A)
    rw [map_natCast] at h
    simp only [Nat.cast_zero, zero_mul, add_zero]
    exact_mod_cast h
  | succ h ih =>
    rw [Nat.mul_succ] at hr
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (show d + m ≤ r by omega)
    obtain ⟨P, B, hA⟩ := split_form A
    obtain ⟨P₁, P₂, hP⟩ := split_form P
    have h₁ := one_group P₁ P₂ hm hd hf hab
    have h₂ := ih (by omega : (d + m) * h ≤ l) B
    have h₃ := NNReal.coe_le_coe.mpr (hf (table_add_le (form P) (form B)))
    rw [← hA, map_add, NNReal.coe_add, hP] at h₃
    rw [Nat.cast_succ, Nat.cast_add, Nat.cast_add]
    linarith only [h₁, h₂, h₃]

end Speedup

theorem grouped_price {K : Type} [Field K] [Infinite K]
    (X : Fin 3 → Type) [∀ s, Fintype (X s)] (T : (∀ s, X s) → K) {d g r : ℕ}
    (hd : ∀ s, Fintype.card (X s) ≤ d) (hg : d < g)
    (hr : Tensor.ofRaw (Raw.ofTable X T) ≤ (r : Tensor K (Fin 3)))
    (f : Tensor K (Fin 3) →+* NNReal) (hf : Monotone f) (a b : Fin 3) (hab : a ≠ b) :
    (f (Tensor.ofRaw (Raw.ofTable X T)) : ℝ) + (r / g : ℕ) *
      ((f (Tensor.wire K a b (g - d)) : ℝ) - (f (Tensor.wire K a b d) : ℝ)) ≤ (r : ℝ) := by
  obtain ⟨A, rfl⟩ := exists_form hr
  apply groups hf hab hd (Nat.sub_pos_of_lt hg) (r / g) _ A
  rw [Nat.add_sub_of_le hg.le]
  exact Nat.mul_div_le _ _

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-!
# The square speedup constant

For groups of size `⌈v s²⌉`, the normalized gain tends to the profile at
`v`. The profile is zero at two and tends to zero at infinity, so its
positive maximum is attained in the open range.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup
open Set Filter
open scoped Topology

private def profile (v : ℝ) := ((v - 1) ^ (3 / 4 : ℝ) - 1) / v

private theorem sample : profile 17 = 7 / 17 := by
  have h : (16 : ℝ) ^ (3 / 4 : ℝ) = 8 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast_mul (by norm_num)]
    norm_num
  unfold profile
  rw [show (17 : ℝ) - 1 = 16 by norm_num, h]
  norm_num

theorem cStar_greatest : IsGreatest {y | ∃ v : ℝ, 2 < v ∧ y = ((v - 1) ^ (3 / 4 : ℝ) - 1) / v} cStar := by
  have ht : ∀ᶠ v : ℝ in atTop, profile v ≤ 7 / 17 := by
    have h := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
    filter_upwards [eventually_ge_atTop (2 : ℝ), h.eventually_lt_const (by norm_num : (0 : ℝ) < 7 / 17)]
      with v hv h'
    have hv' : 0 < v := by linarith
    calc
      profile v ≤ v ^ (3 / 4 : ℝ) / v := by
        unfold profile
        gcongr
        exact (sub_le_self _ zero_le_one).trans (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
      _ = v ^ (-(1 / 4) : ℝ) := by rw [show (-(1 / 4) : ℝ) = 3 / 4 - 1 by norm_num, Real.rpow_sub hv', Real.rpow_one]
      _ ≤ _ := h'.le
  obtain ⟨V, hV⟩ := eventually_atTop.mp ht
  let I := Icc (2 : ℝ) (max 17 V)
  have hi : (17 : ℝ) ∈ I := ⟨by norm_num, le_max_left _ _⟩
  have hc : ContinuousOn profile I := by
    unfold profile
    exact (((continuousOn_id.sub continuousOn_const).rpow_const (fun _ _ => Or.inr (by norm_num))).sub
      continuousOn_const).div continuousOn_id (fun v hv => by change v ≠ 0; linarith [hv.1])
  obtain ⟨v, hv, hm⟩ := isCompact_Icc.exists_isMaxOn ⟨_, hi⟩ hc
  have hmax : 7 / 17 ≤ profile v := sample.symm.trans_le (hm hi)
  have hlt : 2 < v := lt_of_le_of_ne hv.1 (by rintro rfl; norm_num [profile] at hmax)
  have h : IsGreatest {y | ∃ v : ℝ, 2 < v ∧ y = ((v - 1) ^ (3 / 4 : ℝ) - 1) / v} (profile v) := by
    refine ⟨⟨v, hlt, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    by_cases h' : w ≤ max 17 V
    · exact hm ⟨hw.le, h'⟩
    · exact (hV _ ((le_max_right _ _).trans (le_of_not_ge h'))).trans hmax
  rwa [cStar, h.csSup_eq]

theorem cStar_lower : 7 / 17 ≤ cStar :=
  cStar_greatest.2 ⟨17, by norm_num, sample.symm⟩

theorem square_limit {r : ℕ → ℕ}
    (h : ∀ s g : ℕ, 2 ≤ s → 2 * s ^ 2 < g →
      (s : ℝ) ^ (9 / 4 : ℝ) + (⌊(s : ℝ) ^ (9 / 4 : ℝ) / g⌋₊ : ℝ) *
        (((g : ℝ) - (s : ℝ) ^ 2) ^ (3 / 4 : ℝ) - ((s : ℝ) ^ 2) ^ (3 / 4 : ℝ)) ≤ r s)
    {c : ℝ} (hc : c < cStar) :
    ∀ᶠ s : ℕ in atTop, (s : ℝ) ^ (9 / 4 : ℝ) + c * (s : ℝ) ^ (7 / 4 : ℝ) ≤ r s := by
  obtain ⟨v, hv, he⟩ := cStar_greatest.1
  have hv₀ : 0 < v := by linarith
  let g (s : ℕ) := ⌈v * (s : ℝ) ^ 2⌉₊
  let b (s : ℕ) := (g s : ℝ) / (s : ℝ) ^ 2
  let w (s : ℕ) := (s : ℝ) ^ (1 / 4 : ℝ)
  have hs : Tendsto (fun s : ℕ => (s : ℝ) ^ 2) atTop atTop := by
    simpa only [Function.comp_def, Real.rpow_two] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hb : Tendsto b atTop (𝓝 v) := (tendsto_nat_ceil_mul_div_atTop hv₀.le).comp hs
  have hw : Tendsto w atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun s => w s / b s) atTop atTop :=
    hw.atTop_mul_pos (inv_pos.mpr hv₀) (hb.inv₀ hv₀.ne')
  have hfloor := tendsto_nat_floor_div_atTop.comp hratio
  have hterm := ((hb.sub_const 1).rpow_const (p := (3 / 4 : ℝ)) (Or.inr (by norm_num))).sub_const 1
  have hlim := (hfloor.mul hterm).div hb hv₀.ne'
  rw [one_mul, ← he] at hlim
  filter_upwards [eventually_ge_atTop 2, hlim.eventually_const_lt hc] with s hs hlt
  have hs₀ : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hg : 2 * s ^ 2 < g s := by
    apply Nat.lt_ceil.mpr
    push_cast
    exact mul_lt_mul_of_pos_right hv (by positivity)
  have hgs : (s : ℝ) ^ 2 < g s := by exact_mod_cast (show s ^ 2 < g s by omega)
  have hg₀ : 0 < (g s : ℝ) := (sq_nonneg _).trans_lt hgs
  have hw₀ : 0 < w s := by unfold w; positivity
  have hb₀ : 1 < b s := (one_lt_div (by positivity)).mpr hgs
  have h9 : (s : ℝ) ^ (9 / 4 : ℝ) / g s = w s / b s := by
    rw [show (9 / 4 : ℝ) = 1 / 4 + 2 by norm_num, Real.rpow_add hs₀, Real.rpow_two]
    unfold w b
    field_simp
  have h7 : (s : ℝ) ^ (7 / 4 : ℝ) = w s * ((s : ℝ) ^ 2) ^ (3 / 4 : ℝ) := by
    unfold w
    rw [← Real.rpow_natCast_mul hs₀.le, ← Real.rpow_add hs₀]
    norm_num
  have heq : ((g s : ℝ) - (s : ℝ) ^ 2) ^ (3 / 4 : ℝ) =
      (b s - 1) ^ (3 / 4 : ℝ) * ((s : ℝ) ^ 2) ^ (3 / 4 : ℝ) := by
    rw [← Real.mul_rpow (by linarith) (by positivity)]
    unfold b
    congr 1
    field_simp
  refine le_trans ?_ (h s (g s) hs hg)
  apply add_le_add_right
  rw [h9, heq, h7]
  change c < (⌊w s / b s⌋₊ : ℝ) / (w s / b s) * ((b s - 1) ^ (3 / 4 : ℝ) - 1) / b s at hlt
  have h' : c * w s ≤ (⌊w s / b s⌋₊ : ℝ) * ((b s - 1) ^ (3 / 4 : ℝ) - 1) := by
    apply (le_div_iff₀ hw₀).mp
    convert hlt.le using 1
    field_simp
  linarith only [mul_le_mul_of_nonneg_right h' (by positivity : 0 ≤ ((s : ℝ) ^ 2) ^ (3 / 4 : ℝ))]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup
end

section
/-!
# Detecting a full-support product at an ordinary maximizer

Mixed powers of the weighting and ordinary multiplication still have
full support. Their unconditional exact rank lower bound thus detects
a point maximizing the ordinary price without losing weighted price.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Spectral

theorem value_pow (F : Type*) [Field F] {i j k : ℕ} (hi : 0 < i) (hj : 0 < j) (hk : 0 < k)
    (n : ℕ) : value F (i ^ n) (j ^ n) (k ^ n) = (value F i j k) ^ n := by
  have hlog {m : ℕ} (hm : 0 < m) := Real.log_nonneg (by exact_mod_cast hm : 1 ≤ (m : ℝ))
  simp only [value, Nat.cast_pow, Real.log_pow]
  rw [homogeneous F (hlog hi) (hlog hj) (hlog hk) (Nat.cast_nonneg _), Real.exp_nat_mul]

variable {F : Type} [Field F] {i j k : ℕ}

theorem tensor_price {f : Point F} (hf : Monotone f) (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    (f (tensor F i j k) : ℝ) = Real.exp (score f (Real.log i) (Real.log j) (Real.log k)) := by
  have h (a b : Fin 3) {n : ℕ} (hn : 0 < n) :
      (f (Tensor.wire F a b n) : ℝ) = Real.exp (Real.log n * dist f a b) :=
    (Tensor.price_wire _ (mono_real hf) a b hn).trans (Real.rpow_def_of_pos (by positivity) _)
  rw [tensor, f.map_mul, f.map_mul, NNReal.coe_mul, NNReal.coe_mul, h _ _ hi, h _ _ hj,
    h _ _ hk, score, Real.exp_add, Real.exp_add]

def Covers (i j k : ℕ) (A : Tensor F (Fin 3)) : Prop :=
  ∃ w : Fin i → Fin j → Fin k → F, (∀ a b c, w a b c ≠ 0) ∧ weightedTensor w ≤ A

theorem Covers.mul {i' j' k' I J K : ℕ} {A B : Tensor F (Fin 3)}
    (h : Covers i j k A) (h' : Covers i' j' k' B)
    (hi : I = i * i') (hj : J = j * j') (hk : K = k * k') : Covers I J K (A * B) := by
  obtain ⟨x, hx, hx'⟩ := h
  obtain ⟨y, hy, hy'⟩ := h'
  obtain ⟨z, hz, hz'⟩ := tensor_full hx hy hi hj hk
  refine ⟨z, hz, hz'.trans ((Tensor.mul_le_mul_left _ _ _ hy').trans ?_)⟩
  rw [mul_comm, mul_comm A]
  exact Tensor.mul_le_mul_left _ _ _ hx'

theorem Covers.pow {A : Tensor F (Fin 3)} (h : Covers i j k A) (n : ℕ) :
    Covers (i ^ n) (j ^ n) (k ^ n) (A ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero]
    refine ⟨fun _ _ _ => 1, fun _ _ _ => one_ne_zero, ?_⟩
    have h₁ := ordinary_le_tensor F (i := 1) (j := 1) (k := 1) (by decide) (by decide) (by decide)
    simpa [tensor, Tensor.wire, Tensor.shared_one] using h₁
  | succ n ih =>
    rw [pow_succ A]
    exact ih.mul h (pow_succ _ _) (pow_succ _ _) (pow_succ _ _)

theorem weighted_maximizer {w : Fin i → Fin j → Fin k → F} (hw : ∀ a b c, w a b c ≠ 0)
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    ∃ f : Point F, Monotone f ∧ value F i j k ≤ (f (weightedTensor w) : ℝ) ∧
      (f (tensor F i j k) : ℝ) = value F i j k := by
  have hρ : 0 < value F i j k := Real.exp_pos _
  refine simultaneous hρ hρ ?_ ?_
  · intro f hf
    rw [tensor_price hf hi hj hk, value, Real.exp_le_exp]
    exact score_le_exponent hf (Real.log_nonneg (by exact_mod_cast hi))
      (Real.log_nonneg (by exact_mod_cast hj)) (Real.log_nonneg (by exact_mod_cast hk))
  intro m n r hr
  have h₁ : Covers i j k (weightedTensor w) := ⟨w, hw, le_rfl⟩
  have h₂ : Covers i j k (tensor F i j k) :=
    ⟨_, fun _ _ _ => one_ne_zero, ordinary_le_tensor F hi hj hk⟩
  have hm := h₁.mul (h₂.pow m) (pow_succ' i m) (pow_succ' j m) (pow_succ' k m)
  obtain ⟨v, hv, hv'⟩ := hm.pow n
  have hR : WeightedRankLE v r := (wtensor_le_iff (coefficients v)).mp (hv'.trans hr)
  have hh := hR.full hv (pow_pos (pow_pos hi _) _) (pow_pos (pow_pos hj _) _)
    (pow_pos (pow_pos hk _) _)
  change value F _ _ _ ≤ r at hh
  rwa [value_pow F (pow_pos hi _) (pow_pos hj _) (pow_pos hk _),
    value_pow F hi hj hk, pow_succ'] at hh

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-! # Mixed products of full-support and ordinary tensors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Spectral Filter
open scoped Topology

variable {F : Type} [Field F] {A B : Tensor F (Fin 3)}

def Dominates (A B : Tensor F (Fin 3)) : Prop :=
  ∃ i j k, 0 < i ∧ 0 < j ∧ 0 < k ∧ Covers i j k A ∧ B = tensor F i j k

theorem Dominates.mul {A' B' : Tensor F (Fin 3)} (h : Dominates A B) (h' : Dominates A' B') :
    Dominates (A * A') (B * B') := by
  obtain ⟨i, j, k, hi, hj, hk, h, rfl⟩ := h
  obtain ⟨i', j', k', hi', hj', hk', h', rfl⟩ := h'
  refine ⟨i * i', j * j', k * k', by positivity, by positivity, by positivity, h.mul h' rfl rfl rfl, ?_⟩
  simp only [tensor, Tensor.wire, Tensor.shared_mul]
  exact (mul_mul_mul_comm _ _ _ _).trans (congrArg (· * _) (mul_mul_mul_comm _ _ _ _))

theorem Dominates.pow (h : Dominates A B) (m : ℕ) : Dominates (A ^ m) (B ^ m) := by
  obtain ⟨i, j, k, hi, hj, hk, h, rfl⟩ := h
  exact ⟨_, _, _, pow_pos hi _, pow_pos hj _, pow_pos hk _, h.pow m, (tensor_power _ _ _ _ _).symm⟩

theorem Dominates.price (h : Dominates A B) {f : Point F} (hf : Monotone f) :
    ∃ g : Point F, Monotone g ∧ (f B : ℝ) ≤ g A := by
  obtain ⟨i, j, k, hi, hj, hk, ⟨w, hw, hw'⟩, rfl⟩ := h
  obtain ⟨g, hg, hg', _⟩ := weighted_maximizer hw hi hj hk
  refine ⟨g, hg, le_trans ?_ (hg'.trans (NNReal.coe_le_coe.mpr (hg hw')))⟩
  rw [tensor_price hf hi hj hk, value, Real.exp_le_exp]
  exact score_le_exponent hf (Real.log_nonneg (by exact_mod_cast hi))
    (Real.log_nonneg (by exact_mod_cast hj)) (Real.log_nonneg (by exact_mod_cast hk))

theorem Dominates.pos {f : Point F} (h : Dominates A B) (hf : Monotone f) :
    0 < (f B : ℝ) := by
  obtain ⟨i, j, k, hi, hj, hk, _, rfl⟩ := h
  rw [tensor_price hf hi hj hk]
  exact Real.exp_pos _

theorem Dominates.one_le {f : Point F} (h : Dominates A B) (hf : Monotone f) :
    1 ≤ (f A : ℝ) := by
  obtain ⟨g, _, hg⟩ := h.price hf
  have hA : A ≠ 0 := by
    intro he
    have hp := (h.pos hf).trans_le hg
    simp [he] at hp
  have he := hf (Tensor.one_le A hA)
  rw [map_one] at he
  exact_mod_cast he

/-- A uniform linear upper bound on two log-prices transfers from
the full-support weightings to their ordinary products. Integer
multiplicities approximate any nonnegative real slope. -/
theorem Dominates.line {C D : Tensor F (Fin 3)} (h : Dominates A B) (h' : Dominates C D)
    {t b : ℝ} (ht : 0 ≤ t)
    (hu : ∀ f : Point F, Monotone f → Real.log (f A) + t * Real.log (f C) ≤ b)
    {g : Point F} (hg : Monotone g) :
    Real.log (g B) + t * Real.log (g D) ≤ b := by
  have hp : Tendsto (fun n : ℕ => (⌊t * n⌋₊ : ℝ) / n) atTop (𝓝 t) :=
    (tendsto_nat_floor_mul_div_atTop ht).comp tendsto_natCast_atTop_atTop
  apply le_of_tendsto ((hp.mul_const (Real.log (g D))).const_add (Real.log (g B)))
  filter_upwards [eventually_gt_atTop 0] with n hn
  let m := ⌊t * n⌋₊
  obtain ⟨f, hf, hf'⟩ := ((h.pow n).mul (h'.pow m)).price hg
  simp only [g.map_mul, f.map_mul, map_pow, NNReal.coe_mul, NNReal.coe_pow] at hf'
  have hgB := h.pos hg
  have hgD := h'.pos hg
  have hfA := h.one_le hf
  have hfC := h'.one_le hf
  have he := Real.log_le_log (by positivity) hf'
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at he
  simp only [Real.log_pow] at he
  have hn' : 0 < (n : ℝ) := by positivity
  have hh : (m : ℝ) ≤ t * n := Nat.floor_le (by positivity)
  have hh' := mul_le_mul_of_nonneg_right hh (Real.log_nonneg hfC)
  have hf' := mul_le_mul_of_nonneg_left (hu f hf) hn'.le
  change Real.log (g B) + (m : ℝ) / n * Real.log (g D) ≤ b
  field_simp
  linarith only [he, hh', hf']

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-! # Right-hand slopes of the three-side exponent -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter Set Spectral
open scoped Topology

@[simp] theorem vary_zero (L : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) (e : Fin 3) :
    vary L a b c e 0 = L a b c := by
  fin_cases e <;> simp [vary]

variable {F : Type} [Field F] {a b c t : ℝ}

private theorem maximizing (F : Type) [Field F] (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∃ f : Point F, Monotone f ∧ score f a b c = exponent F a b c := by
  obtain ⟨x, y, z, h, he⟩ := (support F).attains ha hb hc
  obtain ⟨f, hf, hf'⟩ := h.score (a := a) (b := b) (c := c)
  exact ⟨f, hf, hf'.symm.trans he⟩

def edge (e : Fin 3) : Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)] e

theorem edge_ne (e : Fin 3) : (edge e).1 ≠ (edge e).2 := by fin_cases e <;> decide

theorem vary_score (f : Point F) (e : Fin 3) (a b c t : ℝ) :
    vary (score f) a b c e t = score f a b c + t * dist f (edge e).1 (edge e).2 := by
  fin_cases e <;> simp [vary, score, edge] <;> ring

theorem vary_max (F : Type) [Field F] (e : Fin 3) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ht : 0 ≤ t) :
    ∃ f : Point F, Monotone f ∧ vary (score f) a b c e t = vary (exponent F) a b c e t := by
  fin_cases e
  · exact maximizing F (add_nonneg ha ht) hb hc
  · exact maximizing F ha (add_nonneg hb ht) hc
  · exact maximizing F ha hb (add_nonneg hc ht)

private theorem vary_le {f : Point F} (hf : Monotone f) (e : Fin 3)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (ht : 0 ≤ t) :
    vary (score f) a b c e t ≤ vary (exponent F) a b c e t := by
  fin_cases e
  · exact score_le_exponent hf (add_nonneg ha ht) hb hc
  · exact score_le_exponent hf ha (add_nonneg hb ht) hc
  · exact score_le_exponent hf ha hb (add_nonneg hc ht)

/-- A maximum of affine price functions has an increasing secant slope.
The slope at zero is interpreted from the positive side, even on a face. -/
theorem partialRight_spec (F : Type) [Field F] (e : Fin 3)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let X := vary (exponent F) a b c e
    let d := partialRight (exponent F) a b c e
    HasDerivWithinAt X d (Ici 0) 0 ∧ 0 ≤ d ∧ ∀ t, 0 ≤ t → X 0 + t * d ≤ X t := by
  intro X d
  let Q t := (X t - X 0) / t
  have hnon (t : ℝ) (ht : 0 < t) : 0 ≤ Q t := by
    obtain ⟨f, hf, he⟩ := vary_max F e ha hb hc (le_rfl : (0 : ℝ) ≤ 0)
    have hu := vary_le hf e ha hb hc ht.le
    rw [vary_score, zero_mul, add_zero] at he
    rw [vary_score, he] at hu
    exact div_nonneg (sub_nonneg.mpr ((le_add_of_nonneg_right
      (mul_nonneg ht.le (dist_bounds hf _ _).1)).trans hu)) ht.le
  have hm : MonotoneOn Q (Ioi 0) := by
    intro s hs t ht hst
    obtain ⟨f, hf, he⟩ := vary_max F e ha hb hc hs.le
    have h₀ := vary_le hf e ha hb hc (le_rfl : (0 : ℝ) ≤ 0)
    have h₁ := vary_le hf e ha hb hc ht.le
    rw [vary_score, zero_mul, add_zero] at h₀
    rw [vary_score] at he h₁
    unfold Q X
    rw [div_le_div_iff₀ hs ht, ← he]
    linarith only [mul_le_mul_of_nonneg_right h₀ (sub_nonneg.mpr hst),
      mul_le_mul_of_nonneg_right h₁ hs.le]
  have hbdd : BddBelow (Q '' Ioi 0) := ⟨0, by rintro _ ⟨t, ht, rfl⟩; exact hnon t ht⟩
  let b := sInf (Q '' Ioi 0)
  have hd : HasDerivWithinAt X b (Ici 0) 0 := by
    apply HasDerivWithinAt.Ici_of_Ioi
    apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
    have he : _root_.slope X 0 = Q := by ext t; rw [slope_def_field, sub_zero]
    rw [he]
    exact hm.tendsto_nhdsGT hbdd
  have he : d = b := hd.derivWithin (uniqueDiffWithinAt_Ici 0)
  rw [he]
  refine ⟨hd, le_csInf ⟨_, 1, by norm_num, rfl⟩ ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hnon t ht
  · intro t ht
    rcases eq_or_lt_of_le ht with rfl | ht
    · simp
    have he : b ≤ Q t := csInf_le hbdd ⟨t, ht, rfl⟩
    linarith only [(le_div_iff₀ ht).mp he]

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
# Grouped speedup for geometric border rank

Take a point maximizing the ordinary tensor while detecting the weighting.
An orientation with largest wire exponent achieves at least the average
exponent weighted by the three logarithmic side lengths. Spectral
sublevels are closed, so the group estimate survives geometric closure.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Spectral

private theorem ZClosure.ungroup {F : Type} [Field F] {i j k : ℕ}
    {A : Set (Coordinates i j k → F)} {T : Coordinates i j k → F}
    (h : ZClosure A T) : ZClosure ((fun v => v ∘ ungroup) '' A) (T ∘ ungroup) := by
  intro p hp
  rw [← MvPolynomial.eval_rename]
  apply h
  intro t ht
  rw [MvPolynomial.eval_rename]
  exact hp _ ⟨t, ht, rfl⟩

private theorem best_wire {F : Type} [Field F] {i j k : ℕ} {f : Point F}
    (hf : Monotone f) (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) (hvol : 1 < i * j * k)
    (h : (f (tensor F i j k) : ℝ) = value F i j k) :
    ∃ a b : Fin 3, a ≠ b ∧ slope F i j k ≤ dist f a b := by
  let d := max (dist f 0 1) (max (dist f 0 2) (dist f 1 2))
  have h₁ : dist f 0 1 ≤ d := le_max_left _ _
  have h₂ : dist f 0 2 ≤ d := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : dist f 1 2 ≤ d := (le_max_right _ _).trans (le_max_right _ _)
  have he : slope F i j k ≤ d := by
    unfold slope
    apply (div_le_iff₀ (Real.log_pos (by exact_mod_cast hvol))).2
    rw [← h, tensor_price hf hi hj hk, Real.log_exp, score, Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by positivity) (by positivity)]
    have hlog {m : ℕ} (hm : 0 < m) := Real.log_nonneg (by exact_mod_cast hm : 1 ≤ (m : ℝ))
    linarith only [mul_le_mul_of_nonneg_left h₁ (hlog hi), mul_le_mul_of_nonneg_left h₂ (hlog hj),
      mul_le_mul_of_nonneg_left h₃ (hlog hk)]
  rcases le_max_iff.mp he with h | h
  · exact ⟨0, 1, by decide, h⟩
  rcases le_max_iff.mp h with h | h
  · exact ⟨0, 2, by decide, h⟩
  · exact ⟨1, 2, by decide, h⟩

theorem slope_nonneg (F : Type*) [Field F] {i j k : ℕ} (hi : 0 < i) (hj : 0 < j) (hk : 0 < k)
    (hvol : 1 < i * j * k) : 0 ≤ slope F i j k := by
  have hlog {m : ℕ} (hm : 0 < m) := Real.log_nonneg (by exact_mod_cast hm : 1 ≤ (m : ℝ))
  have h := (bounds F (hlog hi) (hlog hj) (hlog hk)).1
  rw [slope, value, Real.log_exp]
  exact div_nonneg ((add_nonneg (hlog hi) (hlog hj)).trans ((le_max_left _ _).trans h))
    (Real.log_pos (by exact_mod_cast hvol)).le

private theorem gain_mono {x d a b : ℝ} (hd : 1 ≤ d) (hx : d ≤ x)
    (ha : 0 ≤ a) (hab : a ≤ b) : x ^ a - d ^ a ≤ x ^ b - d ^ b := by
  have hgap : 0 ≤ b - a := sub_nonneg.mpr hab
  have hd' := zero_lt_one.trans_le hd
  have hx' := hd'.trans_le hx
  have he (y : ℝ) (hy : 0 < y) : y ^ b - y ^ a = y ^ a * (y ^ (b - a) - 1) := by
    rw [mul_sub, ← Real.rpow_add hy, add_sub_cancel, mul_one]
  have h : d ^ b - d ^ a ≤ x ^ b - x ^ a := by
    rw [he d hd', he x hx']
    exact mul_le_mul (Real.rpow_le_rpow hd'.le hx ha)
      (sub_le_sub_right (Real.rpow_le_rpow hd'.le hx hgap) 1)
      (sub_nonneg.mpr (Real.one_le_rpow hd hgap)) (by positivity)
  linarith

theorem closure_grouped {K : Type} [Field K] [Infinite K] {i j k r d g : ℕ}
    {u : Fin i → Fin j → Fin k → K} (hu : ZClosure (rankSet K i j k r) (coefficients u))
    (hmax : largest i j k ≤ d) (hd : 0 < d) (hg' : d < g)
    (f : Point K) (hf : Monotone f) {x y : Fin 3} (hxy : x ≠ y) :
    (f (weightedTensor u) : ℝ) + (r / g : ℕ) *
      (((g : ℝ) - d) ^ dist f x y - (d : ℝ) ^ dist f x y) ≤ r := by
  let gain := (f (Tensor.wire K x y (g - d)) : ℝ) - (f (Tensor.wire K x y d) : ℝ)
  let B := (r : ℝ) - (r / g : ℕ) * gain
  have hp (v) (hv : v ∈ rankSet K i j k r) : (f (wtensor v) : ℝ) ≤ B := by
    exact le_sub_iff_add_le.mpr (grouped_price _ _ (fun s => (legs_card i j k s).trans hmax) hg'
      ((wtensor_le_iff v).mpr hv) f hf x y hxy)
  have hB : 0 ≤ B := by
    have h₀ : (0 : Coordinates i j k → K) ∈ rankSet K i j k r := ⟨0, 0, 0, by simp⟩
    exact (NNReal.coe_nonneg _).trans (hp 0 h₀)
  have hprice : (f (weightedTensor u) : ℝ) ≤ B :=
    hu.ungroup.price f hf hB (by rintro _ ⟨v, hv, rfl⟩; exact hp v hv)
  have he : gain = ((g : ℝ) - d) ^ dist f x y - (d : ℝ) ^ dist f x y := by
    have hw' {n : ℕ} (hn : 0 < n) : (f (Tensor.wire K x y n) : ℝ) = (n : ℝ) ^ dist f x y :=
      Tensor.price_wire _ (mono_real hf) _ _ hn
    unfold gain
    rw [hw' (Nat.sub_pos_of_lt hg'), hw' hd, Nat.cast_sub hg'.le]
  rw [← he]
  exact le_sub_iff_add_le.mp hprice

theorem group_count {ρ : ℝ} {r g : ℕ} (hρ : 0 < ρ) (hr : ρ ≤ r) (hg : 0 < g) :
    ⌊ρ / g⌋₊ ≤ r / g := by
  apply (Nat.le_div_iff_mul_le hg).mpr
  have hg₀ : 0 < (g : ℝ) := by positivity
  exact_mod_cast ((le_div_iff₀ hg₀).mp (Nat.floor_le (div_nonneg hρ.le hg₀.le))).trans hr

variable {F : Type*} [Field F] {i j k r : ℕ} {w : Fin i → Fin j → Fin k → F}

/-- The grouped bound holds with the actual exponent, without assuming
a formula for its value. -/
theorem BorderRankLE.grouped (h : BorderRankLE w r) (hw : ∀ a b c, w a b c ≠ 0)
    (hvol : 1 < i * j * k) {g : ℕ} (hg : 2 * largest i j k < g) :
    let d := largest i j k
    let ρ := value F i j k
    let a := slope F i j k
    ρ + (⌊ρ / g⌋₊ : ℝ) * (((g : ℝ) - d) ^ a - (d : ℝ) ^ a) ≤ r := by
  intro d ρ a
  have hi : 0 < i := Nat.pos_of_ne_zero (by rintro rfl; simp at hvol)
  have hj : 0 < j := Nat.pos_of_ne_zero (by rintro rfl; simp at hvol)
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hvol)
  have hd : 0 < d := (Nat.mul_pos hi hj).trans_le (le_max_left _ _)
  have hg' : d < g := by omega
  have hr : ρ ≤ r := h.full hw hi hj hk
  have hρ : 0 < ρ := Real.exp_pos _
  have ha : 0 ≤ a := slope_nonneg F hi hj hk hvol
  obtain ⟨K, _, _, alg, u, hs, hu⟩ := h.small
  have hu' (x y z) : u x y z ≠ 0 := fun he => hw x y z ((hs x y z).mp he)
  have hlog {m : ℕ} (hm : 0 < m) := Real.log_nonneg (by exact_mod_cast hm : 1 ≤ (m : ℝ))
  have he : value K i j k = ρ := by
    rw [value, ← exponent_extension K (AlgebraicClosure F) (hlog hi) (hlog hj) (hlog hk),
      exponent_extension F (AlgebraicClosure F) (hlog hi) (hlog hj) (hlog hk)]
    rfl
  have he' : slope K i j k = a := by rw [slope, he]; rfl
  obtain ⟨f, hf, hf', heq⟩ := weighted_maximizer hu' hi hj hk
  obtain ⟨x, y, hxy, hθ⟩ := best_wire hf hi hj hk hvol heq
  rw [he'] at hθ
  rw [he] at hf'
  have hprice := closure_grouped hu le_rfl hd hg' f hf hxy
  have hcount := group_count hρ hr (hd.trans hg')
  have hgd : (d : ℝ) ≤ g - d := by
    have hh : 2 * (d : ℝ) < g := by exact_mod_cast hg
    linarith
  have hgain := gain_mono (by exact_mod_cast hd) hgd ha hθ
  have h₀ := sub_nonneg.mpr (Real.rpow_le_rpow (Nat.cast_nonneg _) hgd ha)
  have hh := mul_le_mul (Nat.cast_le.mpr hcount) hgain h₀ (Nat.cast_nonneg _)
  exact (add_le_add hf' hh).trans hprice

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
# Speedup with any one-sided slope

Linearize both terms of the grouped price bound at the proposed
ordinary value and directional slope. The resulting linear upper
bound on log-prices transfers to the ordinary product by mixed powers.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Spectral Set

private theorem ordinary_dominates (F : Type) [Field F] (i j k : ℕ)
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    Dominates (tensor F i j k) (tensor F i j k) :=
  ⟨i, j, k, hi, hj, hk, ⟨_, fun _ _ _ => one_ne_zero, ordinary_le_tensor F hi hj hk⟩, rfl⟩

private theorem wire_dominates (F : Type) [Field F] (e : Fin 3) :
    let W := Tensor.wire F (edge e).1 (edge e).2 2
    Dominates W W := by
  fin_cases e
  · simpa [edge, tensor, Tensor.wire, Tensor.shared_one] using
      ordinary_dominates F 2 1 1 (by decide) (by decide) (by decide)
  · simpa [edge, tensor, Tensor.wire, Tensor.shared_one] using
      ordinary_dominates F 1 2 1 (by decide) (by decide) (by decide)
  · simpa [edge, tensor, Tensor.wire, Tensor.shared_one] using
      ordinary_dominates F 1 1 2 (by decide) (by decide) (by decide)

private theorem closure_directional {F : Type} [Field F] [Infinite F] {i j k r g : ℕ}
    {w : Fin i → Fin j → Fin k → F} (h : ZClosure (rankSet F i j k r) (coefficients w))
    (hw : ∀ a b c, w a b c ≠ 0) (hi : 0 < i) (hj : 0 < j) (hk : 0 < k)
    (hg : 2 * largest i j k < g) (e : Fin 3) :
    let d := largest i j k
    let θ := partialRight (exponent F) (Real.log i) (Real.log j) (Real.log k) e
    value F i j k + (r / g : ℕ) * (((g : ℝ) - d) ^ θ - (d : ℝ) ^ θ) ≤ r := by
  intro d θ
  let ρ := value F i j k
  let q : ℝ := (r / g : ℕ)
  let B := ((g : ℝ) - d) ^ θ - (d : ℝ) ^ θ
  let W := Tensor.wire F (edge e).1 (edge e).2 2
  let A := weightedTensor w
  have hA : Dominates A (tensor F i j k) := ⟨i, j, k, hi, hj, hk, ⟨w, hw, le_rfl⟩, rfl⟩
  have hW : Dominates W W := wire_dominates F e
  have hl {m : ℕ} (hm : 0 < m) := Real.log_nonneg (by exact_mod_cast hm : 1 ≤ (m : ℝ))
  obtain ⟨_, hθ, hvar⟩ := partialRight_spec F e (hl hi) (hl hj) (hl hk)
  have hd : 0 < d := (Nat.mul_pos hi hj).trans_le (le_max_left _ _)
  have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hg' : (d : ℝ) ≤ g - d := by
    have : 2 * (d : ℝ) ≤ g := by exact_mod_cast hg.le
    linarith
  obtain ⟨t, ht, hline⟩ := Speedup.gain_tangent hd' hg' hθ
  have hρ : 0 < ρ := Real.exp_pos _
  have hq : 0 ≤ q := Nat.cast_nonneg _
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let s := q * t / ρ
  have hs : 0 ≤ s := div_nonneg (mul_nonneg hq ht) hρ.le
  have he : ρ * s = q * t := mul_div_cancel₀ _ hρ.ne'
  let b := ((r : ℝ) - ρ - q * B) / ρ + Real.log ρ + s * θ
  have hwlog (f : Point F) : s / Real.log 2 * Real.log (f W) = s * dist f (edge e).1 (edge e).2 := by
    change _ = s * (Real.log (f W) / Real.log 2)
    ring
  have hu (f : Point F) (hf : Monotone f) : Real.log (f A) + s / Real.log 2 * Real.log (f W) ≤ b := by
    let z := dist f (edge e).1 (edge e).2
    have h₁ := closure_grouped h le_rfl hd (show d < g by omega) f hf (edge_ne e)
    have h₂ := mul_le_mul_of_nonneg_left (hline z) hq
    have h₃ := Speedup.log_tangent hρ (zero_lt_one.trans_le (hA.one_le hf))
    change (f A : ℝ) + q * (((g : ℝ) - d) ^ z - (d : ℝ) ^ z) ≤ r at h₁
    change q * (B + t * (z - θ)) ≤ q * (((g : ℝ) - d) ^ z - (d : ℝ) ^ z) at h₂
    rw [hwlog]
    change Real.log (f A) + s * z ≤ b
    apply le_of_mul_le_mul_left _ hρ
    unfold b
    rw [mul_add, mul_add, mul_add, mul_div_cancel₀ _ hρ.ne', ← mul_assoc, ← mul_assoc, he]
    linarith only [h₁, h₂, h₃]
  obtain ⟨f, hf, hscore⟩ := vary_max F e (hl hi) (hl hj) (hl hk) hs
  have hb := hA.line hW (div_nonneg hs htwo.le) hu hf
  rw [tensor_price hf hi hj hk, Real.log_exp, hwlog, ← vary_score, hscore] at hb
  have hh := (hvar _ hs).trans hb
  rw [vary_zero] at hh
  have hval : exponent F (Real.log i) (Real.log j) (Real.log k) = Real.log ρ :=
    (Real.log_exp _).symm
  rw [hval] at hh
  change Real.log ρ + s * θ ≤ ((r : ℝ) - ρ - q * B) / ρ + Real.log ρ + s * θ at hh
  have h₀ : 0 ≤ ((r : ℝ) - ρ - q * B) / ρ := by linarith only [hh]
  change ρ + q * B ≤ r
  linarith only [(le_div_iff₀ hρ).mp h₀]

theorem vary_congr {X Y : ℝ → ℝ → ℝ → ℝ} {a b c : ℝ} (e : Fin 3)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : ∀ x y z, 0 ≤ x → 0 ≤ y → 0 ≤ z → X x y z = Y x y z) :
    EqOn (vary X a b c e) (vary Y a b c e) (Ici 0) := by
  intro t ht
  fin_cases e
  · exact he _ _ _ (add_nonneg ha ht) hb hc
  · exact he _ _ _ ha (add_nonneg hb ht) hc
  · exact he _ _ _ ha hb (add_nonneg hc ht)

/-- Every one-sided partial derivative can replace the average
exponent. In particular one may take the largest of the three. -/
theorem BorderRankLE.directional {F : Type*} [Field F] {i j k r g : ℕ}
    {w : Fin i → Fin j → Fin k → F} (h : BorderRankLE w r) (hw : ∀ a b c, w a b c ≠ 0)
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) (hg : 2 * largest i j k < g) (e : Fin 3) :
    let d := largest i j k
    let ρ := value F i j k
    let θ := partialRight (exponent F) (Real.log i) (Real.log j) (Real.log k) e
    HasDerivWithinAt (vary (exponent F) (Real.log i) (Real.log j) (Real.log k) e) θ (Ici 0) 0 ∧
      ρ + (⌊ρ / g⌋₊ : ℝ) * (((g : ℝ) - d) ^ θ - (d : ℝ) ^ θ) ≤ r := by
  intro d ρ θ
  obtain ⟨K, _, _, alg, u, hs, hu⟩ := h.small
  have hw' (a b c) : u a b c ≠ 0 := fun he => hw a b c ((hs a b c).mp he)
  have hl {m : ℕ} (hm : 0 < m) := Real.log_nonneg (by exact_mod_cast hm : 1 ≤ (m : ℝ))
  have he (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
      exponent K a b c = exponent F a b c := by
    rw [← exponent_extension K (AlgebraicClosure F) ha hb hc,
      exponent_extension F (AlgebraicClosure F) ha hb hc]
  have hv : value K i j k = ρ := congrArg Real.exp (he _ _ _ (hl hi) (hl hj) (hl hk))
  have heq := vary_congr e (hl hi) (hl hj) (hl hk) he
  have hθ : partialRight (exponent K) (Real.log i) (Real.log j) (Real.log k) e = θ :=
    derivWithin_congr heq (heq (mem_Ici.mpr le_rfl))
  obtain ⟨hd, hpos, _⟩ := partialRight_spec K e (hl hi) (hl hj) (hl hk)
  rw [hθ] at hd hpos
  refine ⟨hd.congr_of_mem heq.symm (mem_Ici.mpr le_rfl), ?_⟩
  have hb := closure_directional hu hw' hi hj hk hg e
  rw [hv, hθ] at hb
  have hgd : (d : ℝ) ≤ g - d := by
    have : 2 * (d : ℝ) ≤ g := by exact_mod_cast hg.le
    linarith
  have hcount := group_count (show 0 < ρ from Real.exp_pos _) (h.full hw hi hj hk) (by omega : 0 < g)
  have hgain := sub_nonneg.mpr (Real.rpow_le_rpow (Nat.cast_nonneg _) hgd hpos)
  exact le_trans (add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount) hgain) ρ) hb

theorem BorderRankLE.directional_benchmark {F : Type*} [Field F] {i j k r g : ℕ}
    {w : Fin i → Fin j → Fin k → F} (h : BorderRankLE w r) (hw : ∀ a b c, w a b c ≠ 0)
    (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) (hg : 2 * largest i j k < g) (e : Fin 3) :
    let d := largest i j k
    let ρ := Real.exp (U (Real.log i) (Real.log j) (Real.log k))
    let θ := partialRight U (Real.log i) (Real.log j) (Real.log k) e
    HasDerivWithinAt (vary U (Real.log i) (Real.log j) (Real.log k) e) θ (Ici 0) 0 ∧
      ρ + (⌊ρ / g⌋₊ : ℝ) * (((g : ℝ) - d) ^ θ - (d : ℝ) ^ θ) ≤ r := by
  have hl {m : ℕ} (hm : 0 < m) := Real.log_nonneg (by exact_mod_cast hm : 1 ≤ (m : ℝ))
  have he := vary_congr e (hl hi) (hl hj) (hl hk) (fun _ _ _ => all_shapes hr hs)
  obtain ⟨hd, hb⟩ := h.directional hw hi hj hk hg e
  have hθ : partialRight (exponent F) (Real.log i) (Real.log j) (Real.log k) e =
      partialRight U (Real.log i) (Real.log j) (Real.log k) e :=
    derivWithin_congr he (he (mem_Ici.mpr le_rfl))
  rw [hθ] at hd hb
  rw [value, all_shapes hr hs (hl hi) (hl hj) (hl hk)] at hb
  exact ⟨hd.congr_of_mem he.symm (mem_Ici.mpr le_rfl), hb⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
# Strict speedup and the square surplus

If the asymptotic minimum exceeds every leg dimension, take a power
where it exceeds three times the largest dimension. At least one full
group then gives a strictly positive gain.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter

variable {F : Type u} [Field F] {i j k r : ℕ} {w : Fin i → Fin j → Fin k → F}

private theorem largest_power (i j k n : ℕ) :
    largest (i ^ n) (j ^ n) (k ^ n) ≤ (largest i j k) ^ n := by
  simp only [largest, ← mul_pow]
  refine max_le ?_ (max_le ?_ ?_) <;> gcongr <;> omega

theorem BorderRankLE.strict (h : BorderRankLE w r) (hw : ∀ a b c, w a b c ≠ 0)
    (hvol : 1 < i * j * k) (hgap : (largest i j k : ℝ) < value F i j k) :
    value F i j k < (r : ℝ) := by
  have hi : 0 < i := Nat.pos_of_ne_zero (by rintro rfl; simp at hvol)
  have hj : 0 < j := Nat.pos_of_ne_zero (by rintro rfl; simp at hvol)
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hvol)
  have hd : 0 < (largest i j k : ℝ) := by unfold largest; positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 : ℝ) ((one_lt_div hd).mpr hgap)
  have hn₀ : n ≠ 0 := by rintro rfl; norm_num at hn
  rw [div_pow, lt_div_iff₀ (pow_pos hd n), ← value_pow F hi hj hk] at hn
  let d := largest (i ^ n) (j ^ n) (k ^ n)
  let ρ := value F (i ^ n) (j ^ n) (k ^ n)
  let a := slope F (i ^ n) (j ^ n) (k ^ n)
  have hvol' : 1 < i ^ n * j ^ n * k ^ n := by rw [← mul_pow, ← mul_pow]; exact one_lt_pow₀ hvol hn₀
  have hd' : 0 < d := by unfold d largest; positivity
  have hd₁ : 1 ≤ (d : ℝ) := by exact_mod_cast hd'
  have hρ : 3 * (d : ℝ) < ρ := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (by exact_mod_cast largest_power i j k n) (by norm_num)) hn
  have ha : 0 < a := by
    apply div_pos (Real.log_pos (by linarith : 1 < ρ))
    exact Real.log_pos (by exact_mod_cast hvol')
  have hw' : ∀ x y z, WPower w n x y z ≠ 0 := by
    intro x y z
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => hw _ _ _)
  have he := BorderRankLE.grouped (h.pow n) hw' hvol' (show 2 * d < 3 * d by omega)
  change ρ + (⌊ρ / (3 * d : ℕ)⌋₊ : ℝ) *
    ((((3 * d : ℕ) : ℝ) - d) ^ a - (d : ℝ) ^ a) ≤ ((r ^ n : ℕ) : ℝ) at he
  push_cast at he
  have hfloor : 0 < ⌊ρ / (3 * (d : ℝ))⌋₊ :=
    (Nat.one_le_floor_iff _).mpr ((one_le_div (by positivity)).mpr hρ.le)
  have hg : (d : ℝ) ^ a < (3 * d - (d : ℝ)) ^ a :=
    Real.rpow_lt_rpow (by positivity) (by linarith) ha
  have hl : ρ < (r : ℝ) ^ n := (lt_add_of_pos_right _ (mul_pos (by positivity) (sub_pos.mpr hg))).trans_le he
  unfold ρ at hl
  rw [value_pow F hi hj hk] at hl
  exact (pow_lt_pow_iff_left₀ (hd.trans hgap).le (Nat.cast_nonneg _) hn₀).mp hl

theorem square_value (F : Type*) [Field F] {s : ℕ} (hs : 0 < s) :
    value F s s s = (s : ℝ) ^ MatrixExponent.omega F :=
  (ordinary_rank F hs hs hs).symm.trans (ordinary_square F hs)

theorem square_slope (F : Type*) [Field F] {s : ℕ} (hs : 2 ≤ s)
    (hω : MatrixExponent.omega F = 9 / 4) : slope F s s s = 3 / 4 := by
  have hs' : 1 < (s : ℝ) := by exact_mod_cast hs
  have hlog := Real.log_pos hs'
  rw [slope, square_value F (by omega), hω, Real.log_rpow (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  field_simp
  ring

theorem square_border_surplus {K : ℕ → Type u} [∀ n, Field (K n)]
    (hsq : ∀ n, MatrixExponent.omega (K n) = 9 / 4)
    (w : ∀ n, Fin n → Fin n → Fin n → K n) (hw : ∀ n a b c, w n a b c ≠ 0)
    (r : ℕ → ℕ) (hr : ∀ n, BorderRankLE (w n) (r n)) {c : ℝ} (hc : c < Speedup.cStar) :
    ∀ᶠ s : ℕ in atTop, (s : ℝ) ^ (9 / 4 : ℝ) + c * (s : ℝ) ^ (7 / 4 : ℝ) ≤ r s := by
  apply Speedup.square_limit _ hc
  intro s g hs hg
  have hd : largest s s s = s ^ 2 := by simp [largest, pow_two]
  have hvol : 1 < s * s * s := by
    rw [show s * s * s = s ^ 3 by ring]
    exact one_lt_pow₀ (by omega) (by decide)
  have he := BorderRankLE.grouped (hr s) (hw s) hvol (g := g) (by rwa [hd])
  simpa only [hd, Nat.cast_pow, square_value (K s) (by omega : 0 < s),
    square_slope (K s) hs (hsq s), hsq s] using he

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end
