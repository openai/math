import OAI.LinearAlgebra.MatrixExponent.Rectangle.Rows
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Dual
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Price
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law
import OAI.LinearAlgebra.TensorSpectrum.TagGrowth
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Mask

/-!
# Geometric border rank

Take Zariski closure in the space of all three-tensor coefficients over
the algebraic closure, including the coefficients outside the multiplication
support. The Veronese span bound gives an exact decomposition of every
power at polynomial overhead. This overhead disappears in the limit.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k r : ℕ}

variable {w : Fin i → Fin j → Fin k → F}

theorem WeightedRankLE.border (hr : WeightedRankLE w r) : BorderRankLE w r :=
  fun _ h => h _ (hr.map (algebraMap F (AlgebraicClosure F)))

open Border in
private theorem closure_pow (h : ZClosure (rankSet F i j k r) (coefficients w)) (n : ℕ) :
    rankW (WPower w n) ≤ (n + 1) ^ Fintype.card (Coordinates i j k) * r ^ n := by
  obtain ⟨d, hd, y, c, hy, he⟩ := h.power n
  choose A B C hABC using fun t => rankSet_power (hy t) n
  have hr : WeightedRankLE (WPower w n) (d * r ^ n) := by
    let e : Fin (d * r ^ n) ≃ Fin d × Fin (r ^ n) := finProdFinEquiv.symm
    refine ⟨fun t x => c (e t).1 * A (e t).1 (e t).2 x,
      fun t y => B (e t).1 (e t).2 y, fun t z => C (e t).1 (e t).2 z, ?_⟩
    intro x y' z
    change _ = coefficients (WPower w n) (x, y', z)
    rw [← coefficients_pow, he, ← e.symm.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.apply_symm_apply]
    apply Finset.sum_congr rfl
    intro t _
    change _ = c t * powerTable (y t) n (x, y', z)
    rw [← hABC, Finset.mul_sum]
    simp only [mul_assoc]
  exact (rankW_le hr).trans (Nat.mul_le_mul_right _ hd)

/-- In geometric border rank the decompositions can use the algebraic
closure. Specialization and field descent remove that scalar extension. -/
theorem BorderRankLE.asymptotic (h : BorderRankLE w r) (hi : 0 < i) (hj : 0 < j)
    (hk : 0 < k) : asymptoticRank w ≤ r := by
  rcases (supportSize w).eq_zero_or_pos with he | he
  · rw [asymptotic_zero he]; positivity
  have hw : 0 < Rectangle.density w := by unfold Rectangle.density; positivity
  have hp : 0 < asymptoticRank w := lt_of_lt_of_le (by positivity) (asymptotic_density hi hj hk hw)
  apply TensorSpectrum.le_of_pow_le_polynomial_mul_pow _ _ 1 (Fintype.card (Coordinates i j k))
    (by positivity) hp.le (by norm_num) (by positivity)
  intro n hn
  have hr := rankW_spec (WPower (extend (AlgebraicClosure F) w) n)
  rw [one_mul, Real.rpow_natCast]
  exact (extension_lower hr hi hj hk hw hn).trans (by exact_mod_cast closure_pow h n)

theorem BorderRankLE.density (h : BorderRankLE w r) (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    Rectangle.density w * Real.exp (exponent F (Real.log i) (Real.log j) (Real.log k)) ≤ r := by
  rcases le_or_gt (Rectangle.density w) 0 with hw | hw
  · exact (mul_nonpos_of_nonpos_of_nonneg hw (Real.exp_nonneg _)).trans (by positivity)
  · exact (asymptotic_density hi hj hk hw).trans (h.asymptotic hi hj hk)

theorem BorderRankLE.full (h : BorderRankLE w r) (hw : ∀ a b c, w a b c ≠ 0)
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    Real.exp (exponent F (Real.log i) (Real.log j) (Real.log k)) ≤ r := by
  have hd := h.density hi hj hk
  rwa [Rectangle.density, full_size hw, Nat.cast_mul, Nat.cast_mul,
    div_self (by positivity), one_mul] at hd

theorem cell_bound (F : Type*) [Field F] : CellBound F :=
  cells_of_closed (fun K _ _ => (closed_fulfills K).cells) F

/-- The product on any set of whole output cells pays at least for the
most nearly square rectangle of the same area. -/
theorem ZClosure.cells (h : ZClosure (rankSet F i j k r) (coefficients w)) {u : Finset (Pos i j)}
    (hu : u.Nonempty) (hw : ∀ x y z, w x y z ≠ 0 ↔ (x, y) ∈ u)
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    Real.exp (exponent F (short i j u.card) (Real.log u.card - short i j u.card)
      (Real.log k)) ≤ r := by
  obtain ⟨ha, hb⟩ := short_bounds hi hj hu.card_pos
  have hc : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  apply TensorSpectrum.le_of_pow_le_polynomial_mul_pow _ _ 1 (Fintype.card (Coordinates i j k))
    (by positivity) (by positivity) (by norm_num) (by positivity)
  intro n _
  obtain ⟨s, hs, hs'⟩ := power_cells hw hk n
  have hs₀ : s.Nonempty := Finset.card_pos.mp (hs.symm ▸ pow_pos hu.card_pos n)
  have hh := cell_bound F _ _ _ _ (pow_pos hi n) (pow_pos hj n) (pow_pos hk n) _ s hs₀ hs'
    (rankW_spec (WPower w n))
  simp only [hs, short_pow, Nat.cast_pow, Real.log_pow, ← mul_sub] at hh
  rw [homogeneous F ha (sub_nonneg.mpr hb) hc (Nat.cast_nonneg _), Real.exp_nat_mul] at hh
  rw [one_mul, Real.rpow_natCast]
  exact hh.trans (by exact_mod_cast closure_pow h n)

theorem BorderRankLE.cells (h : BorderRankLE w r) {u : Finset (Pos i j)}
    (hu : u.Nonempty) (hw : ∀ x y z, w x y z ≠ 0 ↔ (x, y) ∈ u)
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    Real.exp (exponent F (short i j u.card) (Real.log u.card - short i j u.card)
      (Real.log k)) ≤ r := by
  let K := AlgebraicClosure F
  let v x y z := algebraMap F K (w x y z)
  have hv (x y z) : v x y z ≠ 0 ↔ (x, y) ∈ u := by simpa [v] using hw x y z
  obtain ⟨ha, hb⟩ := short_bounds hi hj hu.card_pos
  have hc : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  rw [← exponent_extension F K ha (sub_nonneg.mpr hb) hc]
  exact ZClosure.cells h hu hv hi hj hk

theorem BorderRankLE.surplus (h : BorderRankLE w r) (hw : ∀ a b c, w a b c ≠ 0)
    {q : ℕ} (hq : 0 < q) (hk : 0 < k) (hq' : q ≤ i * j) :
    Real.exp (exponent F (short i j q) (Real.log q - short i j q) (Real.log k)) - q ≤
      (r : ℝ) - (i : ℝ) * j := by
  have hi : 0 < i := Nat.pos_of_ne_zero (by rintro rfl; simp at hq'; omega)
  have hj : 0 < j := Nat.pos_of_ne_zero (by rintro rfl; simp at hq'; omega)
  obtain ⟨harea, u, he, hcut⟩ := h.delete hw hk hq'
  have hu : u.Nonempty := Finset.card_pos.mp (he.symm ▸ hq)
  have hm (x y z) : mask w u x y z ≠ 0 ↔ (x, y) ∈ u := by simp [mask, hw]
  have hl := hcut.cells hu hm hi hj hk
  rw [he, Nat.cast_sub ((Nat.sub_le _ _).trans harea), Nat.cast_sub hq', Nat.cast_mul] at hl
  linarith

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
# Geometric border rank at the harmonic threshold

Choose the retained area as a product of rounded side lengths.
Trimming the longer side, or both sides equally at a square, makes
these the most nearly square lengths that fit at that area.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter

private theorem short_left {i j a b : ℕ} (ha : 0 < a) (hab : a ≤ b) (hi : a ≤ i) (hj : b ≤ j)
    (he : a = i ∨ a = b) : short i j (a * b) = Real.log a := by
  have hb := ha.trans_le hab
  have hlog {s t : ℕ} (hs : 0 < s) (h : s ≤ t) : Real.log s ≤ Real.log t :=
    Real.log_le_log (by positivity) (by exact_mod_cast h)
  rw [short, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  apply le_antisymm _ (le_min (le_min (hlog ha hi) (hlog ha (hab.trans hj)))
    (by linarith [hlog ha hab]))
  rcases he with he | he
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans_eq (by rw [he]))
  · exact (min_le_right _ _).trans_eq (by rw [he]; ring)

private theorem trim_longer (u : ℝ) {x y : ℝ} (hxy : x < y) :
    ∀ᶠ n : ℕ in atTop, side n x ≤ trimmed n y u := by
  have h := (tendsto_rpow_atTop (sub_pos.mpr hxy)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0, h.eventually_ge_atTop (Real.exp u)] with n hn he
  apply Nat.ceil_mono
  rw [Real.exp_neg, le_inv_mul_iff₀ (Real.exp_pos _)]
  change Real.exp u ≤ (n : ℝ) ^ (y - x) at he
  rwa [Real.rpow_sub (by positivity), le_div_iff₀ (by positivity)] at he

private theorem exponent_short (F : Type*) [Field F] {i j a b k : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (h : short i j (a * b) = Real.log a ∨ short i j (a * b) = Real.log b) :
    exponent F (short i j (a * b)) (Real.log (a * b : ℕ) - short i j (a * b)) (Real.log k) =
      exponent F (Real.log a) (Real.log b) (Real.log k) := by
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  rcases h with h | h
  · rw [h, add_sub_cancel_left]
  · rw [h, add_sub_cancel_right]
    exact transpose _ (Real.log_nonneg (by exact_mod_cast hb))
      (Real.log_nonneg (by exact_mod_cast ha)) (Real.log_nonneg (by exact_mod_cast hk))

private theorem border_shift {K : ℕ → Type*} [∀ n, Field (K n)] {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    (hrig : ∀ n, Rigidity (K n)) (hsq : ∀ n, MatrixExponent.omega (K n) = 9 / 4)
    {b : ℝ} {a : ℕ → ℕ} (ha : ∀ n, 0 < n → 0 < a n)
    (hlog : Tendsto (fun n => Real.log (a n) - x * y * Real.log n) atTop (nhds (b * (x * y))))
    (w : ∀ n, Fin (side n x) → Fin (side n y) → Fin (a n) → K n)
    (hw : ∀ n a b c, w n a b c ≠ 0) (r : ℕ → ℕ) (hr : ∀ n, BorderRankLE (w n) (r n))
    {L : ℝ} (hL : L < Threshold.optimum b (min (x / y) (y / x))) :
    ∀ᶠ n in atTop, L < normalized x y r n := by
  have hl (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
      (h : L < Real.exp (-s - t) * (max (b + (y / x) * s + (x / y) * t) 0) ^ 2 / 4)
      (hfit : ∀ᶠ n : ℕ in atTop,
        let a := trimmed n x s
        let b := trimmed n y t
        let z := short (side n x) (side n y) (a * b)
        z = Real.log a ∨ z = Real.log b) :
      ∀ᶠ n in atTop, L < normalized x y r n := by
    filter_upwards [eventually_gt_atTop 0, (trimmed_shifted_surplus_limit hx hy hxy hlog s t).eventually
      (lt_mem_nhds h), hfit] with n hn hn' hfit'
    have hi := trimmed_pos hn x s
    have hj := trimmed_pos hn y t
    have hk := ha n hn
    have hd := (hr n).surplus (hw n) (Nat.mul_pos hi hj) hk
      (Nat.mul_le_mul (trimmed_le n x hs) (trimmed_le n y ht))
    have hlog {i : ℕ} (h : 0 < i) : 0 ≤ Real.log (i : ℝ) :=
      Real.log_nonneg (by exact_mod_cast h)
    rw [exponent_short _ hi hj hk hfit', Nat.cast_mul,
      all_shapes (hrig n) (hsq n) (hlog hi) (hlog hj) (hlog hk)] at hd
    have hA : 1 ≤ (side n x : ℝ) * side n y := by
      exact_mod_cast Nat.mul_pos (side_pos hn x) (side_pos hn y)
    exact hn'.trans_le (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hd
      (Real.log_nonneg hA)) (by positivity))
  let C := min (x / y) (y / x)
  have hC : 0 < C := by unfold C; positivity
  obtain ⟨u, hu, he⟩ := (Threshold.maximum b hC).2.1
  have hbound : L < Threshold.gain b C u := he.symm ▸ hL
  unfold Threshold.gain C at hbound
  rcases lt_trichotomy x y with h | rfl | h
  · apply hl 0 u le_rfl hu
    · have hh : x / y ≤ y / x := by gcongr
      simpa [min_eq_left hh] using hbound
    · filter_upwards [eventually_gt_atTop 0, trim_longer u h] with n hn he
      left
      rw [trimmed_zero]
      exact short_left (side_pos hn x) he le_rfl (trimmed_le n y hu) (.inl rfl)
  · apply hl (u / 2) (u / 2) (by positivity) (by positivity)
    · simpa [show -(u / 2) - u / 2 = -u by ring, div_self hx.ne', add_assoc] using hbound
    · filter_upwards [eventually_gt_atTop 0] with n hn
      left
      have h' := trimmed_le n x (show 0 ≤ u / 2 by positivity)
      exact short_left (trimmed_pos hn x _) le_rfl h' h' (.inr rfl)
  · apply hl u 0 hu le_rfl
    · have hh : y / x ≤ x / y := by gcongr
      simpa [min_eq_right hh] using hbound
    · filter_upwards [eventually_gt_atTop 0, trim_longer u h] with n hn he
      right
      rw [trimmed_zero]
      rw [show short (side n x) (side n y) (trimmed n x u * side n y) =
        short (side n y) (side n x) (side n y * trimmed n x u) by simp [short, min_comm, mul_comm]]
      exact short_left (side_pos hn y) he le_rfl (trimmed_le n x hu) (.inl rfl)

theorem scaled_border_surplus {K : ℕ → Type*} [∀ n, Field (K n)] {x y a : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) (ha : 0 < a)
    (hrig : ∀ n, Rigidity (K n)) (hsq : ∀ n, MatrixExponent.omega (K n) = 9 / 4)
    (w : ∀ n, Fin (side n x) → Fin (side n y) → Fin (Threshold.width n x y a) → K n)
    (hw : ∀ n a b c, w n a b c ≠ 0) (r : ℕ → ℕ) (hr : ∀ n, BorderRankLE (w n) (r n))
    {L : ℝ} (hL : L < Threshold.optimum (Real.log a / (x * y)) (min (x / y) (y / x))) :
    ∀ᶠ n in atTop, L < normalized x y r n := by
  apply border_shift hx hy hxy hrig hsq _ (Threshold.log_width hx hy ha) w hw r hr hL
  intro n hn
  exact Nat.ceil_pos.mpr (by positivity)

/-- The border-rank half of the harmonic threshold corollary. -/
theorem border_surplus {K : ℕ → Type*} [∀ n, Field (K n)] {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    (hrig : ∀ n, Rigidity (K n)) (hsq : ∀ n, MatrixExponent.omega (K n) = 9 / 4)
    (w : ∀ n, Fin (side n x) → Fin (side n y) → Fin (side n (x * y)) → K n)
    (hw : ∀ n a b c, w n a b c ≠ 0) (r : ℕ → ℕ) (hr : ∀ n, BorderRankLE (w n) (r n))
    {L : ℝ} (hL : L < Real.exp (-2) * min ((x / y) ^ 2) ((y / x) ^ 2)) :
    ∀ᶠ n in atTop, L < normalized x y r n := by
  refine border_shift hx hy hxy hrig hsq (b := 0) (fun n hn => side_pos hn (x * y))
    (by simpa using log_side (mul_pos hx hy)) w hw r hr ?_
  rw [Threshold.optimum, ite_eq_left (by positivity), zero_div, zero_sub, mul_comm]
  rcases le_total (x / y) (y / x) with h | h
  · simpa only [min_eq_left h, min_eq_left (pow_le_pow_left₀ (by positivity) h 2)] using hL
  · simpa only [min_eq_right h, min_eq_right (pow_le_pow_left₀ (by positivity) h 2)] using hL

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end
