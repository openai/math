import OAI.LinearAlgebra.MatrixExponent.FieldExtension
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Rows


/-!
# The spectral formula for the arithmetic exponent

For a fixed integer format the tensor is the product of the three
wires. Rounding the dimensions up costs a factor of at most eight at
every spectral point. Strict spectral comparison and block recursion
turn a uniform spectral upper bound into an arithmetic one.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter Spectral
open scoped NNReal

variable {F : Type} [Field F] {f : Point F} {a b c s : ℝ}

private theorem rounded_wire (hf : Monotone f) {n : ℕ} (hn : 0 < n) (ha : 0 ≤ a)
    (i j : Fin 3) :
    (n : ℝ) ^ (a * dist f i j) ≤ f (Tensor.wire F i j (side n a)) ∧
    (f (Tensor.wire F i j (side n a)) : ℝ) ≤ 2 * (n : ℝ) ^ (a * dist f i j) := by
  have he : (f (Tensor.wire F i j (side n a)) : ℝ) = (side n a : ℝ) ^ dist f i j :=
    Tensor.price_wire _ (mono_real hf) i j (side_pos hn a)
  rw [he, Real.rpow_mul (by positivity)]
  obtain ⟨hl, hu⟩ := dist_bounds hf i j
  refine ⟨Real.rpow_le_rpow (by positivity) (Nat.le_ceil _) hl, ?_⟩
  calc
    _ ≤ (2 * (n : ℝ) ^ a) ^ dist f i j :=
      Real.rpow_le_rpow (by positivity) (side_le hn ha) hl
    _ = (2 : ℝ) ^ dist f i j * ((n : ℝ) ^ a) ^ dist f i j :=
      Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hu

private theorem rounded_price (hf : Monotone f) {n : ℕ} (hn : 0 < n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let M := tensor F (side n a) (side n b) (side n c)
    (n : ℝ) ^ score f a b c ≤ f M ∧ (f M : ℝ) ≤ 8 * (n : ℝ) ^ score f a b c := by
  have hn₀ : 0 < (n : ℝ) := by positivity
  obtain ⟨la, ua⟩ := rounded_wire hf hn ha 0 1
  obtain ⟨lb, ub⟩ := rounded_wire hf hn hb 0 2
  obtain ⟨lc, uc⟩ := rounded_wire hf hn hc 1 2
  dsimp only
  simp only [score, Real.rpow_add hn₀, tensor, f.map_mul, NNReal.coe_mul]
  constructor
  · gcongr
  · calc
      _ ≤ (2 * (n : ℝ) ^ (a * dist f 0 1)) * (2 * (n : ℝ) ^ (b * dist f 0 2)) *
          (2 * (n : ℝ) ^ (c * dist f 1 2)) := by gcongr
      _ = _ := by ring

theorem score_le_exponent (hf : Monotone f) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    score f a b c ≤ exponent F a b c := by
  by_contra! h
  obtain ⟨n, r, hn, hr, hsave⟩ := (exponent_lt_iff_rank ha hb hc).mp h
  have hn₀ : 0 < n := by omega
  have he := hf ((tensor_le_iff (side_pos hn₀ a) (side_pos hn₀ b) (side_pos hn₀ c)).mpr hr)
  rw [map_natCast] at he
  exact hsave.not_ge ((rounded_price hf hn₀ ha hb hc).1.trans (by exact_mod_cast he))

theorem price_gap {s t : ℝ} (hs : 0 ≤ s) (hlt : s < t) :
    ∃ n r : ℕ, 2 ≤ n ∧ 8 * (n : ℝ) ^ s < r ∧ (r : ℝ) < (n : ℝ) ^ t := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (t - s)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hlt)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn, hp⟩ := ((eventually_ge_atTop 2).and (ht.eventually_gt_atTop 10)).exists
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have h₁ := Real.one_le_rpow hn₁ hs
  refine ⟨n, ⌈9 * (n : ℝ) ^ s⌉₊, hn, (lt_of_lt_of_le (by linarith) (Nat.le_ceil _)), ?_⟩
  calc
    _ < 9 * (n : ℝ) ^ s + 1 := Nat.ceil_lt_add_one (by positivity)
    _ ≤ 10 * (n : ℝ) ^ s := by linarith
    _ < (n : ℝ) ^ (t - s) * (n : ℝ) ^ s := mul_lt_mul_of_pos_right hp (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity), sub_add_cancel]

private theorem exponent_le_of_scores (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (h : ∀ f : Point F, Monotone f → score f a b c ≤ s) : exponent F a b c ≤ s := by
  by_contra! hlt
  obtain ⟨n, r, hn, hlo, hhi⟩ := price_gap hs hlt
  have hn₀ : 0 < n := by omega
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn₀
  have hr : 0 < (r : ℝ) := (by positivity : 0 ≤ 8 * (n : ℝ) ^ s).trans_lt hlo
  have hne : (r : Tensor F (Fin 3)) ≠ 0 := by
    intro he
    have hh : r ≤ 0 := (Tensor.natCast_le_iff (K := F) (S := Fin 3) r 0).mp (by simp [he])
    exact hr.not_ge (by exact_mod_cast hh)
  let M := tensor F (side n a) (side n b) (side n c)
  have hp (f : Point F) (hf : Monotone f) : f M < f (r : Tensor F (Fin 3)) := by
    rw [map_natCast]
    apply NNReal.coe_lt_coe.mp
    calc
      (f M : ℝ) ≤ 8 * (n : ℝ) ^ score f a b c := (rounded_price hf hn₀ ha hb hc).2
      _ ≤ 8 * (n : ℝ) ^ s :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn₁ (h f hf)) (by norm_num)
      _ < _ := hlo
  obtain ⟨C, hC⟩ := Spectrum.strictComparison Tensor.add_le_add_right Tensor.mul_le_mul_left
    Tensor.zero_le Tensor.one_le Tensor.exists_bound hne hp
  obtain ⟨p, hp', hsave⟩ := absorb_overhead (D := C) hn hr hhi
  have hR : RankLE F ((side n a) ^ p) ((side n b) ^ p) ((side n c) ^ p) (r ^ p * C) := by
    apply (tensor_le_iff (pow_pos (side_pos hn₀ a) p) (pow_pos (side_pos hn₀ b) p)
      (pow_pos (side_pos hn₀ c) p)).mp
    rw [tensor_power, Nat.cast_mul, Nat.cast_pow, mul_comm]
    exact hC p
  exact lt_irrefl _ (exponent_lt_of_rank ha hb hc hp'
    (hR.cut (side_pow le_rfl p) (side_pow le_rfl p) (side_pow le_rfl p)) hsave)

/-- The exponent is a maximum, with no limit or closure in the set of prices. -/
theorem support (F : Type) [Field F] : Support F (Prices F) := by
  refine ⟨fun h => h.nonneg, ?_, ?_⟩
  · intro a b c x y z ha hb hc h
    obtain ⟨f, hf, he⟩ := h.score (a := a) (b := b) (c := c)
    exact he.trans_le (score_le_exponent hf ha hb hc)
  · intro a b c ha hb hc
    obtain ⟨f, hf, hmax⟩ := maximum_score F a b c
    obtain ⟨x, y, z, hP, he⟩ := score_eq_load (a := a) (b := b) (c := c) hf
    obtain ⟨hx, hy, hz⟩ := hP.nonneg
    have h₀ : 0 ≤ score f a b c := by rw [← he, load]; positivity
    exact ⟨x, y, z, hP, he.trans (le_antisymm (score_le_exponent hf ha hb hc)
      (exponent_le_of_scores ha hb hc h₀ hmax))⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle
