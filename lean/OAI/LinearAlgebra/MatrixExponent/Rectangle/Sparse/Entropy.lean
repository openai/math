import OAI.LinearAlgebra.MatrixExponent.UpperBound
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Dual
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Surplus

section
/-!
# Measuring the support by a weighted count

In a fixed empirical type all three completion counts are constant.
The number of types is polynomial in the power. Consequently the
coloring loss and the cost of selecting a single type disappear.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open OAI.LinearAlgebra.TensorSpectrum.TagWords

theorem degree_bound (F : Type*) [Field F] : DegreeBound F :=
  degrees_of_closed (fun K _ _ => (closed_fulfills K).degrees) F

private theorem average (F : Type*) [Field F] {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    omega F / 3 * (a + b + c) ≤ exponent F a b c := by
  obtain ⟨K, _, ⟨alg⟩⟩ := small_field F
  rw [exponent_extension K F ha hb hc, omega_extension K F]
  have h := Rectangle.support K
  obtain ⟨x, y, z, hp, he⟩ := h.attains zero_le_one zero_le_one zero_le_one
  rw [square] at he
  have h₁ := h.bound ha hb hc hp
  have h₂ := h.bound hb hc ha hp
  have h₃ := h.bound hc ha hb hp
  rw [← cycle K ha hb hc] at h₂
  rw [cycle K hc ha hb] at h₃
  rw [← he]
  unfold load at *
  linarith only [h₁, h₂, h₃]

private theorem scalar {I J K : ℕ} {q r a : ℝ} (hi : 0 < I) (hj : 0 < J) (hk : 0 < K)
    (h : q * Real.exp (a * (Real.log I + Real.log J + Real.log K)) ≤ 432 * (I : ℝ) * J * K * r) :
    q * unitWeight (a - 1) I J K ≤ 432 * r := by
  unfold unitWeight
  rw [sub_mul, one_mul, Real.exp_sub, Real.exp_add, Real.exp_add,
    Real.exp_log (by positivity), Real.exp_log (by positivity), Real.exp_log (by positivity),
    ← mul_div_assoc, div_le_iff₀ (by positivity)]
  linarith only [h]

variable {F : Type*} [Field F] {i j k : ℕ} (w : Fin i → Fin j → Fin k → F)
  (e : Fin (support w).card ≃ support w)

private theorem counted (n : ℕ) :
    (∑ b, weight (support w) e (omega F / 3 - 1) b) ^ n ≤
      432 * ((n : ℝ) + 1) ^ (support w).card * rankW (WPower w n) := by
  let S := support w
  let p := omega F / 3
  let a := weight S e (p - 1)
  obtain ⟨t, ht⟩ := exists_fiberMass_ge_average (N := n) a
  obtain ⟨U, hU, he, h⟩ := Sparse.fiber w e n t
  let I := countWeight (rCount S e) t
  let J := countWeight (cCount S e) t
  let K := countWeight (kCount S e) t
  have hi : 0 < I := Finset.prod_pos (fun l _ => pow_pos (rCount_pos S e l) _)
  have hj : 0 < J := Finset.prod_pos (fun l _ => pow_pos (cCount_pos S e l) _)
  have hk : 0 < K := Finset.prod_pos (fun l _ => pow_pos (kCount_pos S e l) _)
  have hb := degree_bound F _ _ _ I J K _ hi hj hk (WPower w n) U hU
    (fun t ht => (h t ht).1.le) (fun t ht => (h t ht).2.1.le) (fun t ht => (h t ht).2.2.le)
    (rankW_spec (WPower w n))
  have hl {m : ℕ} (hm : 0 < m) := Real.log_nonneg (by exact_mod_cast hm : 1 ≤ (m : ℝ))
  have hp := Real.exp_le_exp.mpr (average F (hl hi) (hl hj) (hl hk))
  have hh := scalar hi hj hk ((mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg U.card)).trans hb)
  have hc : countWeight a t = unitWeight (p - 1) I J K :=
    unit_count _ _ _ _ (rCount_pos S e) (cCount_pos S e) (kCount_pos S e) t
  rw [fiberMass, ← he, hc] at ht
  have hg := (div_le_iff₀ (by positivity)).mp (ht.trans hh)
  exact hg.trans_eq (mul_right_comm _ _ _)

theorem mass_bound (n : ℕ) :
    (∑ b, weight (support w) e (omega F / 3 - 1) b) ^ n ≤ rankW (WPower w n) := by
  have hnon : 0 ≤ ∑ b, weight (support w) e (omega F / 3 - 1) b :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  apply TensorSpectrum.le_of_pow_le_polynomial_mul_pow _ _ (432 * ((n : ℝ) + 1) ^ (support w).card)
    (support w).card (by positivity) (by positivity) (by positivity) (by positivity)
  intro m hm
  rw [← pow_mul, Real.rpow_natCast]
  refine (counted w e (n * m)).trans ?_
  have hr : (rankW (WPower w (n * m)) : ℝ) ≤ (rankW (WPower w n) : ℝ) ^ m := by
    exact_mod_cast rankW_mul w n m hm
  rw [mul_assoc 432 (((n : ℝ) + 1) ^ (support w).card), ← mul_pow, Nat.cast_mul]
  gcongr
  linarith

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

section
/-! # The entropy refinement for sparse weighted products -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open Filter

variable {F : Type*} [Field F] {i j k : ℕ} (w : Fin i → Fin j → Fin k → F)

/-- Natural-log form with the actual arithmetic exponent. -/
theorem entropy_lower (hw : (support w).Nonempty) :
    (support w).card * Real.exp ((omega F / 3 - 1) * conditional (support w)) ≤ asymptoticRank w := by
  obtain ⟨t, ht⟩ := hw
  have hw : (support w).Nonempty := ⟨t, ht⟩
  have hi := Nat.zero_lt_of_lt t.1.isLt
  have hj := Nat.zero_lt_of_lt t.2.1.isLt
  have hk := Nat.zero_lt_of_lt t.2.2.isLt
  have hd : 0 < density w := by
    rw [density, ← card_support]
    exact div_pos (by exact_mod_cast hw.card_pos) (by positivity)
  let S := support w
  let e : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  refine (exp_conditional S e hw _).trans ?_
  apply ge_of_tendsto (tendsto_asymptoticRank hi hj hk hd)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have h : 0 ≤ ∑ b, weight S e (omega F / 3 - 1) b := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  rw [← Real.pow_rpow_inv_natCast h hn.ne']
  exact Real.rpow_le_rpow (pow_nonneg h _) (mass_bound w e n) (by positivity)

/-- The bound in bits from Section 8. No rigidity premise is needed. -/
theorem support_exponent (hω : omega F = 9 / 4) (hw : (support w).Nonempty) :
    (supportSize w : ℝ) ^ (3 / 4 : ℝ) * (2 : ℝ) ^ (premium (support w) / 4) ≤ asymptoticRank w := by
  let S := support w
  have hm : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hw.card_pos
  have ht : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he := entropy_lower w hw
  rw [hω] at he
  rw [← card_support]
  refine le_trans ?_ he
  change (S.card : ℝ) ^ (3 / 4 : ℝ) * (2 : ℝ) ^ (premium S / 4) ≤
    S.card * Real.exp ((9 / 4 / 3 - 1) * conditional S)
  apply le_of_eq
  rw [Real.rpow_def_of_pos hm, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    ← Real.exp_add, premium]
  have hlog : Real.log (S.card : ℝ) * (3 / 4) +
      Real.log 2 * ((Real.log S.card - conditional S) / Real.log 2 / 4) =
      Real.log S.card + (9 / 4 / 3 - 1) * conditional S := by field_simp; ring
  rw [hlog, Real.exp_add, Real.exp_log hm]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

section
/-!
# Preservation of the exponent at subpolynomial density

The lower bound allows both the support and the coefficients to vary
with the size. All-ones weightings attain the exponent even for exact
rank, by taking powers of a single slightly more efficient block.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open Filter

variable (F : Type*) [Field F] {a b c : ℝ}

private theorem rounded_lower (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ exponent F a b c ≤
      Real.exp (exponent F (Real.log (side n a)) (Real.log (side n b)) (Real.log (side n c))) := by
  have h (x : ℝ) : Real.log n * x ≤ Real.log (side n x) := by
    rw [mul_comm, ← Real.log_rpow (by positivity)]
    exact Real.log_le_log (by positivity) (Nat.le_ceil _)
  have h₀ (x : ℝ) : 0 ≤ Real.log (side n x) := Real.log_nonneg (by exact_mod_cast side_pos hn x)
  have hn' : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  obtain ⟨K, _, ⟨alg⟩⟩ := small_field F
  rw [Real.rpow_def_of_pos (by positivity), Real.exp_le_exp,
    exponent_extension K F ha hb hc, exponent_extension K F (h₀ a) (h₀ b) (h₀ c),
    ← homogeneous K ha hb hc hn']
  obtain ⟨x, y, z, hp, he⟩ := (Rectangle.support K).attains (mul_nonneg hn' ha)
    (mul_nonneg hn' hb) (mul_nonneg hn' hc)
  obtain ⟨hx, hy, hz⟩ := hp.nonneg
  rw [← he]
  refine le_trans ?_ ((Rectangle.support K).bound (h₀ a) (h₀ b) (h₀ c) hp)
  unfold load
  gcongr <;> apply h

theorem preservation (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (w : ∀ n, Fin (side n a) → Fin (side n b) → Fin (side n c) → F)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-ε) ≤ density (w n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (exponent F a b c - ε) ≤ asymptoticRank (w n) ∧
      ∀ r, BorderRankLE (w n) r → (n : ℝ) ^ (exponent F a b c - ε) ≤ r := by
  filter_upwards [eventually_gt_atTop 0, h ε hε] with n hn hd
  have hi := side_pos hn a
  have hj := side_pos hn b
  have hk := side_pos hn c
  have hw : 0 < density (w n) := lt_of_lt_of_le (by positivity) hd
  rw [sub_eq_add_neg, add_comm, Real.rpow_add (by positivity)]
  have hl := mul_le_mul hd (rounded_lower F ha hb hc hn) (by positivity) hw.le
  exact ⟨hl.trans (asymptotic_density hi hj hk hw), fun _ hr => hl.trans (hr.density hi hj hk)⟩

theorem ordinary_bounds (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      let w := ordinary F (side n a) (side n b) (side n c)
      density w = 1 ∧ (n : ℝ) ^ exponent F a b c ≤ asymptoticRank w ∧
        asymptoticRank w ≤ rankW w ∧ (rankW w : ℝ) ≤ (n : ℝ) ^ (exponent F a b c + ε) := by
  let t := exponent F a b c + ε / 2
  have ht : 0 ≤ t := by
    have := (le_max_left _ _).trans (bounds F ha hb hc).1
    unfold t; linarith
  obtain ⟨d, r, hd, hr, hr'⟩ := (exponent_lt_iff_rank ha hb hc).mp
    (show exponent F a b c < t by unfold t; linarith)
  have hlim := (tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0, hlim.eventually_ge_atTop (r : ℝ)] with n hn hbig
  intro w
  have hi := side_pos hn a
  have hj := side_pos hn b
  have hk := side_pos hn c
  have hw : ∀ x y z, w x y z ≠ 0 := fun _ _ _ => one_ne_zero
  refine ⟨?_, ?_⟩
  · rw [density, full_size hw, Nat.cast_mul, Nat.cast_mul, div_self (by positivity)]
  rw [ordinary_rank F hi hj hk]
  refine ⟨rounded_lower F ha hb hc hn, (rankW_spec w).full hw hi hj hk, ?_⟩
  obtain ⟨p, hlo, hup⟩ := exists_nat_pow_near (by exact_mod_cast hn : 1 ≤ (n : ℝ))
    (by exact_mod_cast hd : 1 < (d : ℝ))
  have hp {x : ℝ} (hx : 0 ≤ x) : side n x ≤ (side d x) ^ (p + 1) :=
    (Nat.ceil_mono (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hup.le) hx)).trans
      (side_pow le_rfl (p + 1))
  have hh : rankW w ≤ r ^ (p + 1) := rankW_le ((hr.pow (p + 1)).cut (hp ha) (hp hb) (hp hc))
  calc
    _ ≤ (r : ℝ) ^ (p + 1) := by exact_mod_cast hh
    _ ≤ ((d : ℝ) ^ t) ^ p * r := by rw [pow_succ]; gcongr
    _ = ((d : ℝ) ^ p) ^ t * r := by rw [Real.rpow_pow_comm (by positivity)]
    _ ≤ (n : ℝ) ^ t * (n : ℝ) ^ (ε / 2) :=
      mul_le_mul (Real.rpow_le_rpow (by positivity) hlo ht) hbig (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity), show t + ε / 2 = exponent F a b c + ε by unfold t; ring]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end
