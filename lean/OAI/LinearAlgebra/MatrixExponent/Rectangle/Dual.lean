import OAI.LinearAlgebra.MatrixExponent.Rectangle.Weights
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Bounds
import OAI.LinearAlgebra.MatrixExponent.FieldExtension
import OAI.LinearAlgebra.MatrixExponent.Rectangle.FiniteModel
import OAI.LinearAlgebra.MatrixExponent.UpperBound
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Rows
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Threshold
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Support
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law
import Mathlib.Analysis.Subadditive
import OAI.LinearAlgebra.TensorSpectrum.TagGrowth

section
/-!
# Deleting output rows and columns in exact bilinear rank

The output coefficients of a full-support product are independent. The
discarded outputs therefore give independent kernel vectors for the matrix of
restricted rank-one products. A column basis consists of rank-one products
and still spans every retained output.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k i' j' r s : ℕ}

variable {w : Fin i → Fin j → Fin k → F}

private theorem WeightedRankLE.mono (h : WeightedRankLE w r) (hrs : r ≤ s) :
    WeightedRankLE w s := by
  induction s, hrs using Nat.le_induction with
  | base => exact h
  | succ s _ ih =>
    obtain ⟨a, b, c, hc⟩ := ih
    refine ⟨Fin.cons 0 a, Fin.cons 0 b, Fin.cons 0 c, fun x y z => ?_⟩
    simpa [Fin.sum_univ_succ] using hc x y z

private def products (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F) :
    Matrix (Pos i k × Pos k j) (Fin r) F := fun p l => a l p.1 * b l p.2

private theorem compress_products (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F)
    (c : Fin r → Pos i j → F) :
    let d := (products a b).rank
    ∃ (e : Fin d → Fin r) (c' : Fin d → Pos i j → F), ∀ x y z,
      ∑ l, a (e l) x * b (e l) y * c' l z = ∑ l, a l x * b l y * c l z := by
  classical
  let M := products a b
  rw [Matrix.rank_eq_finrank_span_cols]
  obtain ⟨v, hv, heq, _⟩ := Submodule.exists_fun_fin_finrank_span_eq F (Set.range M.col)
  choose e he using hv
  have hmem (z : Pos i j) : ∑ l, c l z • M.col l ∈ Submodule.span F (Set.range v) := by
    rw [heq]
    exact (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨fun l => c l z, rfl⟩
  choose c' hc' using fun z => (Submodule.mem_span_range_iff_exists_fun _).mp (hmem z)
  refine ⟨e, fun l z => c' z l, fun x y z => ?_⟩
  have hz := congrFun (hc' z) (x, y)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← he] at hz
  simpa only [Matrix.col_apply, M, products, mul_comm] using hz

theorem WeightedRankLE.delete (h : WeightedRankLE w r) (hw : ∀ x y z, w x y z ≠ 0)
    (hk : 0 < k) (hi : i' ≤ i) (hj : j' ≤ j) :
    i * j ≤ r ∧ WeightedRankLE (fun x y z => w (Fin.castLE hi x) (Fin.castLE hj y) z)
      (r - (i * j - i' * j')) := by
  classical
  obtain ⟨a, b, c, hc⟩ := h
  let v : Fin k := ⟨0, hk⟩
  let B {α : Type} (z : α → Pos i j) : Matrix (Fin r) α F := fun l t => c l (z t)
  have hind {α : Type} [Fintype α] (z : α → Pos i j) (hinj : Function.Injective z) :
      Fintype.card α ≤ (B z).rank := by
    let A : Matrix α (Fin r) F := fun t l =>
      (w (z t).1 (z t).2 v)⁻¹ * (a l ((z t).1, v) * b l (v, (z t).2))
    have he : A * B z = 1 := by
      ext t u
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [A, B, mul_assoc ((w _ _ _)⁻¹), ← Finset.mul_sum, hc,
        true_and, ← Prod.ext_iff, hinj.eq_iff, mul_ite, mul_zero, inv_mul_cancel₀ (hw _ _ _)]
    simpa only [he, Matrix.rank_one] using Matrix.rank_mul_le_right A (B z)
  constructor
  · simpa [Pos] using (hind id Function.injective_id).trans (B id).rank_le_card_height
  let X (x : Pos i' k) : Pos i k := (Fin.castLE hi x.1, x.2)
  let Y (y : Pos k j') : Pos k j := (y.1, Fin.castLE hj y.2)
  let Z (z : Pos i' j') : Pos i j := (Fin.castLE hi z.1, Fin.castLE hj z.2)
  let a' l x := a l (X x)
  let b' l y := b l (Y y)
  let M := products a' b'
  let D := (Set.range Z)ᶜ
  let z : D → Pos i j := Subtype.val
  have hzero : M * B z = 0 := by
    ext p t
    rw [Matrix.mul_apply, Matrix.zero_apply]
    change ∑ l, a l (X p.1) * b l (Y p.2) * c l (z t) = 0
    rw [hc, ite_eq_right]
    rintro ⟨h₁, _, h₂⟩
    exact t.property ⟨(p.1.1, p.2.2), Prod.ext h₁ h₂⟩
  have hcard : i * j - i' * j' ≤ Fintype.card D := by
    unfold D
    rw [Fintype.card_compl_set]
    simpa [Pos] using Nat.sub_le_sub_left (Fintype.card_range_le Z) (i * j)
  have hbound : M.rank ≤ r - (i * j - i' * j') := by
    have := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzero
    rw [Fintype.card_fin] at this
    have := hind z Subtype.val_injective
    omega
  apply WeightedRankLE.mono _ hbound
  obtain ⟨e, c', he⟩ := compress_products a' b' (fun l p => c l (Z p))
  refine ⟨fun l => a' (e l), fun l => b' (e l), c', fun x y z => ?_⟩
  refine (he x y z).trans ?_
  simpa [a', b', X, Y, Z, Fin.ext_iff] using hc (X x) (Y y) (Z z)

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-! # Rectangular shapes and dual exponents from square equality and rigidity -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {a b c : ℝ}

/-- The square is active, so square equality excludes the strict branch. -/
theorem positive_shapes (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : exponent F a b c = U a b c := by
  rcases hr with h | h
  · exact h a b c ha hb hc
  · have h' := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [U, benchmark])
    rw [square, hs] at h'
    norm_num [U, benchmark] at h'

theorem U_plane (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a = 0 ∨ b = 0 ∨ c = 0) : U a b c = a + b + c := by
  unfold U
  split_ifs with h₁ h₂
  · have : c = 0 := by
      rw [le_min_iff] at h₁
      rcases h with h | h | h <;> linarith [h₁.1, h₁.2]
    simp [this, benchmark]
  · rw [min_eq_left h₂] at h₁
    have : a = 0 := by rcases h with h | h | h <;> linarith
    simp [this, benchmark]
  · rw [min_eq_right (le_of_not_ge h₂)] at h₁
    have : b = 0 := by rcases h with h | h | h <;> linarith
    simp [this, benchmark, add_comm]

theorem all_shapes (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : exponent F a b c = U a b c := by
  by_cases h : a = 0 ∨ b = 0 ∨ c = 0
  · rw [coordinate_plane F ha hb hc h, U_plane ha hb hc h]
  push Not at h
  exact positive_shapes hr hs (ha.lt_of_ne' h.1) (hb.lt_of_ne' h.2.1) (hc.lt_of_ne' h.2.2)

theorem ordered_formula (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    (hc : 0 < c) (h : c ≤ min a b) :
    exponent F a b c = a + b + (max ((a + b) * c - a * b) 0) ^ 2 / (4 * a * b * c) := by
  rw [positive_shapes hr hs (hc.trans_le (le_min_iff.mp h).1) (hc.trans_le (le_min_iff.mp h).2) hc,
    U, ite_eq_left h, benchmark]

theorem threshold (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hc' : c ≤ min a b) :
    exponent F a b c = a + b ↔ c ≤ a * b / (a + b) := by
  rcases eq_or_lt_of_le hc with rfl | hc
  · rw [coordinate_plane F ha.le hb.le le_rfl (Or.inr (Or.inr rfl)), add_zero]
    simp [le_of_lt (div_pos (mul_pos ha hb) (add_pos ha hb))]
  rw [ordered_formula hr hs hc hc', add_eq_left, div_eq_zero_iff, sq_eq_zero_iff,
    or_iff_left (by positivity : 4 * a * b * c ≠ 0), max_eq_right_iff, sub_nonpos,
    le_div_iff₀ (add_pos ha hb), mul_comm c]

/-- The dual exponent is attained, including for nonsquare output. -/
theorem greatest (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    (ha : 0 < a) (hb : 0 < b) :
    IsGreatest {c ∈ Set.Icc 0 (min a b) | exponent F a b c = a + b} (a * b / (a + b)) := by
  have h : 0 ≤ a * b / (a + b) := by positivity
  have h' : a * b / (a + b) ≤ min a b := by
    apply le_min <;> rw [div_le_iff₀ (add_pos ha hb)] <;> nlinarith
  exact ⟨⟨⟨h, h'⟩, (threshold hr hs ha hb h h').mpr le_rfl⟩,
    fun _ hc => (threshold hr hs ha hb hc.1.1 hc.1.2).mp hc.2⟩

theorem dual_eq (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    (ha : 0 < a) (hb : 0 < b) : dual F a b = a * b / (a + b) :=
  (greatest hr hs ha hb).csSup_eq

theorem dual_square (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4) : dual F 1 1 = 1 / 2 := by
  rw [dual_eq hr hs zero_lt_one zero_lt_one]
  norm_num

theorem square_output (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    (hc : 0 ≤ c) (hc' : c ≤ 1) :
    exponent F 1 1 c = if c ≤ 1 / 2 then 2 else 2 + (c - 1 / 2) ^ 2 / c := by
  split_ifs with h
  · have := (threshold hr hs zero_lt_one zero_lt_one hc (le_min hc' hc')).mpr (by linarith)
    linarith
  · rw [ordered_formula hr hs (by linarith) (le_min hc' hc'), max_eq_left (by linarith)]
    ring

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-! Cyclic symmetrization transfers a square lower bound to every shape. -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k r : ℕ} {a b c : ℝ}

theorem RankLE.volume_lower (hr : RankLE F i j k r) (hω : 9 / 4 ≤ omega F) :
    ((i : ℝ) * j * k) ^ (3 / 4 : ℝ) ≤ r := by
  have hs := hr.symmetrize
  rw [← Nat.cast_mul, ← Nat.cast_mul]
  let N := i * j * k
  change MatrixExponent.RankLE F N (r ^ 3) at hs
  change (N : ℝ) ^ (3 / 4 : ℝ) ≤ r
  by_cases hN : 2 ≤ N
  · by_contra! hlt
    apply hω.not_gt
    apply omega_lt_of_rank hN hs
    rw [Nat.cast_pow]
    calc
      (r : ℝ) ^ 3 < ((N : ℝ) ^ (3 / 4 : ℝ)) ^ (3 : ℕ) :=
        pow_lt_pow_left₀ hlt (by positivity) (by decide)
      _ = (N : ℝ) ^ (9 / 4 : ℝ) := by
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
        norm_num
  · have hl := rank_lower hs
    rcases (show N = 0 ∨ N = 1 by omega) with h | h
    · norm_num [h]
    · have hr0 : r ≠ 0 := by rintro rfl; simp [h] at hl
      simpa [h] using (show 1 ≤ (r : ℝ) by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr0)

/-- The mixed derivatives give a rectangular decomposition over a rational
function field. The square exponent is unchanged by this extension. -/
theorem volume_lower (hω : 9 / 4 ≤ omega F) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    3 / 4 * (a + b + c) ≤ exponent F a b c := by
  refine le_csInf ⟨_, volume_admissible F ha hb hc⟩ fun s hs => ?_
  apply le_admissible_of_cost hs
  intro n m hn hm
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr := (bilinearize hm).volume_lower (by rw [omega_extension F]; exact hω)
  calc
    (n : ℝ) ^ (3 / 4 * (a + b + c)) =
        ((n : ℝ) ^ a * (n : ℝ) ^ b * (n : ℝ) ^ c) ^ (3 / 4 : ℝ) := by
      rw [mul_comm, Real.rpow_mul hn₀.le, Real.rpow_add hn₀, Real.rpow_add hn₀]
    _ ≤ ((side n a : ℝ) * side n b * side n c) ^ (3 / 4 : ℝ) := by
      gcongr <;> exact Nat.le_ceil _
    _ ≤ 2 * m := by simpa using hr

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-! # From arbitrary block sides to powers of one fixed format -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

private theorem pad_fixed {n p q i : ℕ} (hn : 2 ≤ n) (hi : 0 < i)
    (hp : (p : ℝ) ≤ q * Real.log n) : i ^ p ≤ (side n (Real.log i)) ^ q := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hi' : 1 ≤ (i : ℝ) := by exact_mod_cast hi
  have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hp (Real.log_nonneg hi'))
  rw [mul_assoc, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by positivity),
    ← Real.rpow_def_of_pos hn'] at h
  have h' := pow_le_pow_left₀ (Real.rpow_nonneg hn'.le (Real.log i))
    (Nat.le_ceil ((n : ℝ) ^ Real.log i)) q
  exact_mod_cast h.trans h'

/-- Every strict bound on the exponent at the logarithmic shape can
be met by the log rank per copy of an actual finite tensor power. -/
theorem fixed_rank {F : Type*} [Field F] {i j k : ℕ} (hi : 0 < i) (hj : 0 < j) (hk : 0 < k)
    {s : ℝ} (h : exponent F (Real.log i) (Real.log j) (Real.log k) < s) :
    ∃ p r : ℕ, 0 < p ∧ RankLE F (i ^ p) (j ^ p) (k ^ p) r ∧ Real.log r / p < s := by
  have hlog {i : ℕ} (hi : 0 < i) : 0 ≤ Real.log (i : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hi)
  obtain ⟨t, ht, ht'⟩ := exists_between h
  obtain ⟨n, r, hn, hr, hrs⟩ := (exponent_lt_iff_rank (hlog hi) (hlog hj) (hlog hk)).mp ht
  have hn₀ : 0 < n := by omega
  have hr₀ : 0 < r := (Nat.mul_pos (side_pos hn₀ _) (side_pos hn₀ _)).trans_le
    (hr.area (side_pos hn₀ _))
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hprice : Real.log r < t * Real.log n := by
    simpa only [Real.log_rpow (by positivity : 0 < (n : ℝ))] using
      Real.log_lt_log (by positivity) hrs
  have ht₀ : 0 < t := pos_of_mul_pos_left ((hlog hr₀).trans_lt hprice) hnlog.le
  obtain ⟨p, hp⟩ := exists_nat_gt (t * Real.log n / (s - t))
  have hp' : 0 < (p : ℝ) := (by positivity : 0 < t * Real.log n / (s - t)).trans hp
  let q := ⌈(p : ℝ) / Real.log n⌉₊
  have hlo : (p : ℝ) ≤ q * Real.log n := (div_le_iff₀ hnlog).mp (Nat.le_ceil _)
  have hhi : (q : ℝ) * Real.log n < p + Real.log n := by
    apply (lt_div_iff₀ hnlog).mp
    rw [add_div, div_self hnlog.ne']
    exact Nat.ceil_lt_add_one (by positivity)
  refine ⟨p, r ^ q, by exact_mod_cast hp', (hr.pow q).cut (pad_fixed hn hi hlo)
    (pad_fixed hn hj hlo) (pad_fixed hn hk hlo), ?_⟩
  rw [Nat.cast_pow, Real.log_pow, div_lt_iff₀ hp']
  linarith only [(div_lt_iff₀ (sub_pos.mpr ht')).mp hp,
    mul_lt_mul_of_pos_left hhi ht₀, mul_le_mul_of_nonneg_left hprice.le (Nat.cast_nonneg q)]

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
# Exact rank surplus at the harmonic threshold

The field and the full-support coefficients may change at every size.
The lower limit statement uses eventual inequalities against every
strictly smaller real constant, so also covers infinite lower limits.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter

theorem density_bound (F : Type*) [Field F] : DensityBound F :=
  density_of_closed (fun K _ _ => (closed_fulfills K).density) F

variable {F : Type*} [Field F] {i j k r : ℕ} {w : Fin i → Fin j → Fin k → F}

theorem full_size (hw : ∀ a b c, w a b c ≠ 0) : supportSize w = i * j * k := by
  simp [supportSize, hw, mul_comm, mul_left_comm]

theorem WeightedRankLE.full (h : WeightedRankLE w r) (hw : ∀ a b c, w a b c ≠ 0)
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    Real.exp (exponent F (Real.log i) (Real.log j) (Real.log k)) ≤ r := by
  have he := density_bound F i j k r hi hj hk w h
  rw [full_size hw, Nat.cast_mul, Nat.cast_mul] at he
  exact le_of_mul_le_mul_left he (by positivity)

theorem WeightedRankLE.surplus (h : WeightedRankLE w r) (hw : ∀ a b c, w a b c ≠ 0)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) (hi : a ≤ i) (hj : b ≤ j) :
    Real.exp (exponent F (Real.log a) (Real.log b) (Real.log k)) - (a : ℝ) * b ≤
      (r : ℝ) - (i : ℝ) * j := by
  obtain ⟨harea, hcut⟩ := h.delete hw hk hi hj
  have he := hcut.full (fun _ _ _ => hw _ _ _) ha hb hk
  rw [Nat.cast_sub ((Nat.sub_le _ _).trans harea), Nat.cast_sub (Nat.mul_le_mul hi hj),
    Nat.cast_mul, Nat.cast_mul] at he
  linarith

private theorem exact_shift {K : ℕ → Type*} [∀ n, Field (K n)] {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    (hrig : ∀ n, Rigidity (K n)) (hsq : ∀ n, MatrixExponent.omega (K n) = 9 / 4)
    {b : ℝ} {a : ℕ → ℕ} (ha : ∀ n, 0 < n → 0 < a n)
    (hlog : Tendsto (fun n => Real.log (a n) - x * y * Real.log n) atTop (nhds (b * (x * y))))
    (w : ∀ n, Fin (side n x) → Fin (side n y) → Fin (a n) → K n)
    (hw : ∀ n a b c, w n a b c ≠ 0) (r : ℕ → ℕ) (hr : ∀ n, WeightedRankLE (w n) (r n))
    {L : ℝ} (hL : L < Threshold.optimum b (max (x / y) (y / x))) :
    ∀ᶠ n in atTop, L < normalized x y r n := by
  have hl (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
      (h : L < Real.exp (-s - t) * (max (b + (y / x) * s + (x / y) * t) 0) ^ 2 / 4) :
      ∀ᶠ n in atTop, L < normalized x y r n := by
    filter_upwards [eventually_gt_atTop 0, (trimmed_shifted_surplus_limit hx hy hxy hlog s t).eventually
      (lt_mem_nhds h)] with n hn hn'
    have hi := trimmed_pos hn x s
    have hj := trimmed_pos hn y t
    have hk := ha n hn
    have hd := (hr n).surplus (hw n) hi hj hk (trimmed_le n x hs) (trimmed_le n y ht)
    have hlog {i : ℕ} (h : 0 < i) : 0 ≤ Real.log (i : ℝ) :=
      Real.log_nonneg (by exact_mod_cast h)
    rw [all_shapes (hrig n) (hsq n) (hlog hi) (hlog hj) (hlog hk)] at hd
    have hA : 1 ≤ (side n x : ℝ) * side n y := by
      exact_mod_cast Nat.mul_pos (side_pos hn x) (side_pos hn y)
    exact hn'.trans_le (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hd
      (Real.log_nonneg hA)) (by positivity))
  let C := max (x / y) (y / x)
  have hC : 0 < C := by unfold C; positivity
  obtain ⟨u, hu, he⟩ := (Threshold.maximum b hC).2.1
  have hbound : L < Threshold.gain b C u := he.symm ▸ hL
  unfold Threshold.gain C at hbound
  rcases le_total (x / y) (y / x) with h | h
  · apply hl u 0 hu le_rfl
    simpa [max_eq_right h] using hbound
  · apply hl 0 u le_rfl hu
    simpa [max_eq_left h] using hbound

theorem scaled_exact_surplus {K : ℕ → Type*} [∀ n, Field (K n)] {x y a : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) (ha : 0 < a)
    (hrig : ∀ n, Rigidity (K n)) (hsq : ∀ n, MatrixExponent.omega (K n) = 9 / 4)
    (w : ∀ n, Fin (side n x) → Fin (side n y) → Fin (Threshold.width n x y a) → K n)
    (hw : ∀ n a b c, w n a b c ≠ 0) (r : ℕ → ℕ) (hr : ∀ n, WeightedRankLE (w n) (r n))
    {L : ℝ} (hL : L < Threshold.optimum (Real.log a / (x * y)) (max (x / y) (y / x))) :
    ∀ᶠ n in atTop, L < normalized x y r n := by
  apply exact_shift hx hy hxy hrig hsq _ (Threshold.log_width hx hy ha) w hw r hr hL
  intro n hn
  exact Nat.ceil_pos.mpr (by positivity)

/-- The exact-rank half of the harmonic threshold corollary. -/
theorem exact_surplus {K : ℕ → Type*} [∀ n, Field (K n)] {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    (hrig : ∀ n, Rigidity (K n)) (hsq : ∀ n, MatrixExponent.omega (K n) = 9 / 4)
    (w : ∀ n, Fin (side n x) → Fin (side n y) → Fin (side n (x * y)) → K n)
    (hw : ∀ n a b c, w n a b c ≠ 0) (r : ℕ → ℕ) (hr : ∀ n, WeightedRankLE (w n) (r n))
    {L : ℝ} (hL : L < Real.exp (-2) * max ((x / y) ^ 2) ((y / x) ^ 2)) :
    ∀ᶠ n in atTop, L < normalized x y r n := by
  refine exact_shift hx hy hxy hrig hsq (b := 0) (fun n hn => side_pos hn (x * y))
    (by simpa using log_side (mul_pos hx hy)) w hw r hr ?_
  rw [Threshold.optimum, ite_eq_left (by positivity), zero_div, zero_sub, mul_comm]
  rcases le_total (x / y) (y / x) with h | h
  · simpa only [max_eq_right h, max_eq_right (pow_le_pow_left₀ (by positivity) h 2)] using hL
  · simpa only [max_eq_left h, max_eq_left (pow_le_pow_left₀ (by positivity) h 2)] using hL

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-! # Homogeneity for the actual arithmetic exponent -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

theorem homogeneous (F : Type*) [Field F] {a b c s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 0 ≤ s) :
    exponent F (s * a) (s * b) (s * c) = s * exponent F a b c := by
  obtain ⟨K, _, ⟨alg⟩⟩ := small_field F
  have ha' := mul_nonneg hs ha
  have hb' := mul_nonneg hs hb
  have hc' := mul_nonneg hs hc
  rw [exponent_extension K F ha hb hc, exponent_extension K F ha' hb' hc']
  have he (x y z : ℝ) : load (s * a) (s * b) (s * c) x y z = s * load a b c x y z := by
    unfold load
    ring
  have hp := support K
  apply le_antisymm
  · obtain ⟨x, y, z, h, heq⟩ := hp.attains ha' hb' hc'
    rw [← heq, he]
    exact mul_le_mul_of_nonneg_left (hp.bound ha hb hc h) hs
  · obtain ⟨x, y, z, h, heq⟩ := hp.attains ha hb hc
    rw [← heq, ← he]
    exact hp.bound ha' hb' hc' h

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-!
# Minimum asymptotic rank over coefficients

The powers have separate row, column and inner indices for every copy.
The density bound holds on every power. Fekete's lemma supplies the
limit, and padding a strict rank witness gives the opposite inequality
for the all-ones weighting.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter
open scoped Topology

variable {F : Type*} [Field F] {i j k : ℕ}

theorem rank_rate {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hadd : ∀ n m, r (n + m) ≤ r n * r m) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (r n : ℝ) ^ (n : ℝ)⁻¹) atTop (𝓝 L) ∧
      ∀ n : ℕ, 0 < n → L ≤ Real.exp (Real.log (r n) / n) := by
  have hp (n) : 0 < (r n : ℝ) := Nat.cast_pos.mpr (hr n)
  let u n := Real.log (r n : ℝ)
  have hs : Subadditive u := by
    intro n m
    unfold u
    rw [← Real.log_mul (hp n).ne' (hp m).ne']
    exact Real.log_le_log (hp _) (by exact_mod_cast hadd n m)
  have hb : BddBelow (Set.range fun n => u n / n) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hr n)) (by positivity)
  refine ⟨Real.exp hs.lim, ?_, fun n hn => Real.exp_le_exp.mpr (hs.lim_le_div hb hn.ne')⟩
  simpa only [u, Real.rpow_def_of_pos (hp _), div_eq_mul_inv] using (hs.tendsto_lim hb).rexp

variable {w : Fin i → Fin j → Fin k → F}

private theorem full_density (hi : 0 < i) (hj : 0 < j) (hk : 0 < k)
    (hw : ∀ a b c, w a b c ≠ 0) : density w = 1 := by
  rw [density, full_size hw, Nat.cast_mul, Nat.cast_mul, div_self (by positivity)]

/-- There is no loss in the density estimate for a power other than
raising the density itself to that power. -/
theorem density_power_lower (w : Fin i → Fin j → Fin k → F)
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) (n : ℕ) :
    (density w * Real.exp (exponent F (Real.log i) (Real.log j) (Real.log k))) ^ n ≤
      rankW (WPower w n) := by
  have hd := density_bound F _ _ _ _ (pow_pos hi n) (pow_pos hj n) (pow_pos hk n) _
    (rankW_spec (WPower w n))
  have hlog {i : ℕ} (hi : 0 < i) : 0 ≤ Real.log (i : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hi)
  rw [supportSize_power] at hd
  simp only [Nat.cast_pow, Real.log_pow] at hd
  rw [homogeneous F (hlog hi) (hlog hj) (hlog hk) (Nat.cast_nonneg _), Real.exp_nat_mul] at hd
  rw [density, mul_pow, div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity),
    mul_pow, mul_pow, mul_comm (rankW _ : ℝ)]
  exact hd

private theorem rate_spec (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) (hw : 0 < density w) :
    Tendsto (fun n : ℕ => (rankW (WPower w n) : ℝ) ^ (n : ℝ)⁻¹) atTop (𝓝 (asymptoticRank w)) ∧
    ∀ n : ℕ, 0 < n → asymptoticRank w ≤ Real.exp (Real.log (rankW (WPower w n)) / n) := by
  have hp (n : ℕ) : 0 < rankW (WPower w n) :=
    Nat.cast_pos.mp (lt_of_lt_of_le (by positivity) (density_power_lower w hi hj hk n))
  obtain ⟨L, hl, hb⟩ := rank_rate hp (rankW_add w)
  rw [asymptoticRank, hl.limUnder_eq]
  exact ⟨hl, hb⟩

theorem tendsto_asymptoticRank (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) (hw : 0 < density w) :
    Tendsto (fun n : ℕ => (rankW (WPower w n) : ℝ) ^ (n : ℝ)⁻¹) atTop (𝓝 (asymptoticRank w)) :=
  (rate_spec hi hj hk hw).1

private theorem zero_limit (hs : supportSize w = 0) :
    Tendsto (fun n : ℕ => (rankW (WPower w n) : ℝ) ^ (n : ℝ)⁻¹) atTop (nhds 0) := by
  classical
  have hw : ∀ b a c, w a b c = 0 := by
    simpa [supportSize, Finset.sum_eq_zero_iff] using hs
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have h : WeightedRankLE (WPower w n) 0 := by
    refine ⟨0, 0, 0, fun x y z => ?_⟩
    simp [WPower, hw, hn.ne']
  rw [Nat.eq_zero_of_le_zero (rankW_le h), Nat.cast_zero, Real.zero_rpow (by positivity)]

theorem asymptotic_zero (hs : supportSize w = 0) : asymptoticRank w = 0 :=
  (zero_limit hs).limUnder_eq

theorem asymptotic_converges (w : Fin i → Fin j → Fin k → F) (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    Tendsto (fun n : ℕ => (rankW (WPower w n) : ℝ) ^ (n : ℝ)⁻¹) atTop (nhds (asymptoticRank w)) := by
  rcases (supportSize w).eq_zero_or_pos with h | h
  · rw [asymptotic_zero h]
    exact zero_limit h
  exact tendsto_asymptoticRank hi hj hk (by unfold density; positivity)

theorem asymptotic_density (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) (hw : 0 < density w) :
    density w * Real.exp (exponent F (Real.log i) (Real.log j) (Real.log k)) ≤ asymptoticRank w := by
  apply ge_of_tendsto (tendsto_asymptoticRank hi hj hk hw)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have h := Real.rpow_le_rpow (by positivity) (density_power_lower w hi hj hk n)
    (by positivity : 0 ≤ (n : ℝ)⁻¹)
  rwa [Real.pow_rpow_inv_natCast (by positivity) hn.ne'] at h

theorem asymptotic_le_power (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) (hw : 0 < density w)
    {n : ℕ} (hn : 0 < n) : asymptoticRank w ^ n ≤ (rankW (WPower w n) : ℝ) := by
  have h := (rate_spec hi hj hk hw).2 n hn
  have hp : 0 < (rankW (WPower w n) : ℝ) :=
    lt_of_lt_of_le (by positivity) (density_power_lower w hi hj hk n)
  have hpos : 0 < asymptoticRank w := lt_of_lt_of_le (by positivity) (asymptotic_density hi hj hk hw)
  rw [div_eq_mul_inv, ← Real.rpow_def_of_pos hp] at h
  have hh := pow_le_pow_left₀ hpos.le h n
  rwa [Real.rpow_inv_natCast_pow hp.le hn.ne'] at hh

theorem ordinary_rank (F : Type*) [Field F] (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    asymptoticRank (ordinary F i j k) =
      Real.exp (exponent F (Real.log i) (Real.log j) (Real.log k)) := by
  let w := ordinary F i j k
  have hd : density w = 1 := full_density hi hj hk (fun _ _ _ => one_ne_zero)
  have hw : 0 < density w := hd.symm ▸ zero_lt_one
  have hlo := asymptotic_density hi hj hk hw
  rw [hd, one_mul] at hlo
  refine le_antisymm ?_ hlo
  by_contra! hlt
  have hpos : 0 < asymptoticRank w := (Real.exp_pos _).trans_le hlo
  obtain ⟨n, r, hn, hr, he⟩ := fixed_rank hi hj hk ((Real.lt_log_iff_exp_lt hpos).mpr hlt)
  have hR : rankW (WPower w n) ≤ r := by
    apply rankW_le
    rw [show WPower w n = (fun _ _ _ => 1) from WPower_one n]
    exact hr
  have hp : 0 < (rankW (WPower w n) : ℝ) :=
    lt_of_lt_of_le (by positivity) (density_power_lower w hi hj hk n)
  have hh := (rate_spec hi hj hk hw).2 n hn
  apply (lt_irrefl (asymptoticRank w))
  calc
    _ ≤ Real.exp (Real.log (rankW (WPower w n)) / n) := hh
    _ ≤ Real.exp (Real.log r / n) := by gcongr
    _ < _ := (Real.lt_log_iff_exp_lt hpos).mp he

/-- At every fixed positive format, the ordinary product attains the
minimum over all full-support weightings. -/
theorem minimum_rank (F : Type*) [Field F] (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    IsLeast {s | ∃ w : Fin i → Fin j → Fin k → F,
        (∀ a b c, w a b c ≠ 0) ∧ asymptoticRank w = s}
      (Real.exp (exponent F (Real.log i) (Real.log j) (Real.log k))) := by
  refine ⟨⟨ordinary F i j k, fun _ _ _ => one_ne_zero, ordinary_rank F hi hj hk⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have hd := full_density hi hj hk hw
  have h := asymptotic_density (w := w) hi hj hk (hd.symm ▸ zero_lt_one)
  rwa [hd, one_mul] at h

/-- The fixed-format minimum in Section 8, using the rectangular law. -/
theorem minimum_eq_benchmark (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    asymptoticRank (ordinary F i j k) = Real.exp (U (Real.log i) (Real.log j) (Real.log k)) ∧
    IsLeast {s | ∃ w : Fin i → Fin j → Fin k → F,
        (∀ a b c, w a b c ≠ 0) ∧ asymptoticRank w = s}
      (Real.exp (U (Real.log i) (Real.log j) (Real.log k))) := by
  rw [← all_shapes hr hs (Real.log_nonneg (by exact_mod_cast hi))
    (Real.log_nonneg (by exact_mod_cast hj)) (Real.log_nonneg (by exact_mod_cast hk))]
  exact ⟨ordinary_rank F hi hj hk, minimum_rank F hi hj hk⟩

theorem ordinary_square (F : Type*) [Field F] (hi : 0 < i) :
    asymptoticRank (ordinary F i i i) = (i : ℝ) ^ MatrixExponent.omega F := by
  have h := homogeneous F zero_le_one zero_le_one zero_le_one
    (Real.log_nonneg (by exact_mod_cast hi : 1 ≤ (i : ℝ)))
  rw [mul_one, square] at h
  rw [ordinary_rank F hi hi hi, h, Real.rpow_def_of_pos (by positivity)]

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-!
# Asymptotic rank under extension of the coefficient field

Specialization fixes the weighting in the base field. The finite
extension may depend on the chosen power, so we take further powers
*after* specialization to pay its degree cost only once.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
    {i j k r n : ℕ} {w : Fin i → Fin j → Fin k → F}

def extend (K : Type*) [Field K] [Algebra F K] (w : Fin i → Fin j → Fin k → F)
    (x : Fin i) (y : Fin j) (z : Fin k) := algebraMap F K (w x y z)

theorem WPower_extend (w : Fin i → Fin j → Fin k → F) (n : ℕ) :
    WPower (extend K w) n = extend K (WPower w n) := by
  funext x y z
  simp only [WPower, extend, map_prod]

theorem density_extend (w : Fin i → Fin j → Fin k → F) : density (extend K w) = density w := by
  unfold density extend
  rw [supportSize_map]

theorem extension_lower (h : WeightedRankLE (WPower (extend K w) n) r)
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) (hw : 0 < density w) (hn : 0 < n) :
    asymptoticRank w ^ n ≤ r := by
  rw [WPower_extend] at h
  obtain ⟨L, _, _, _, hL⟩ := finiteTypeWeighted (algebraMap F K) (WPower w n) h
  have : Module.Finite F L := finite_of_finite_type_of_isJacobsonRing F L
  change WeightedRankLE (extend L (WPower w n)) r at hL
  rw [← WPower_extend] at hL
  let D := Module.finrank F L ^ 2
  have hp : 0 < asymptoticRank w := lt_of_lt_of_le (by positivity) (asymptotic_density hi hj hk hw)
  apply TensorSpectrum.le_of_pow_le_polynomial_mul_pow _ _ (D + 1) 0
    (by positivity) (by positivity) (by positivity) le_rfl
  intro m hm
  let t := rankW (WPower (extend L w) (n * m))
  have ht : t ≤ r ^ m := (rankW_mul (extend L w) n m hm).trans (Nat.pow_le_pow_left (rankW_le hL) _)
  have ht' : WeightedRankLE (extend L (WPower w (n * m))) t := by
    rw [← WPower_extend]
    exact rankW_spec _
  have hd := rankW_le (descendWeighted (F := F) ht')
  rw [← pow_mul, Real.rpow_zero, mul_one]
  calc
    _ ≤ (rankW (WPower w (n * m)) : ℝ) := asymptotic_le_power hi hj hk hw (Nat.mul_pos hn hm)
    _ ≤ (t : ℝ) * D := by exact_mod_cast hd
    _ ≤ (r : ℝ) ^ m * (D + 1) := by gcongr; exact_mod_cast ht; linarith
    _ = _ := mul_comm _ _

theorem asymptotic_extension (K : Type*) [Field K] [Algebra F K]
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    asymptoticRank (extend K w) = asymptoticRank w := by
  rcases (supportSize w).eq_zero_or_pos with h | h
  · have he : supportSize (extend K w) = 0 := (supportSize_map _ _).trans h
    rw [asymptotic_zero he, asymptotic_zero h]
  have hw : 0 < density w := by unfold density; positivity
  have h := tendsto_asymptoticRank hi hj hk hw
  have hw' : 0 < density (extend K w) := by rwa [density_extend]
  have h' := tendsto_asymptoticRank hi hj hk hw'
  apply le_antisymm
  · apply le_of_tendsto_of_tendsto h' h
    filter_upwards [] with n
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    rw [WPower_extend]
    exact_mod_cast rankW_le ((rankW_spec (WPower w n)).map (algebraMap F K))
  · have hp : 0 < asymptoticRank w := lt_of_lt_of_le (by positivity) (asymptotic_density hi hj hk hw)
    apply ge_of_tendsto h'
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← Real.pow_rpow_inv_natCast hp.le hn.ne']
    exact Real.rpow_le_rpow (by positivity)
      (extension_lower (rankW_spec (WPower (extend K w) n)) hi hj hk hw hn) (by positivity)

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-! # Large low-rank rectangles from a strict dual saving -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

theorem rank_of_dual {F : Type*} [Field F] (h : 1 / 2 < dual F 1 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, ∃ s j r : ℕ, n ≤ s ∧
      (s : ℝ) ^ (1 / 2 + ε) ≤ j ∧ (r : ℝ) ≤ (s : ℝ) ^ (2 + δ) ∧ RankLE F s s j r := by
  have hz := coordinate_plane F zero_le_one zero_le_one (le_rfl : (0 : ℝ) ≤ 0)
    (Or.inr (Or.inr rfl))
  obtain ⟨c, ⟨⟨hc, _⟩, he⟩, hlt⟩ := exists_lt_of_lt_csSup
    (show {c ∈ Set.Icc 0 (min 1 1) | exponent F 1 1 c = 1 + 1}.Nonempty from
      ⟨0, by simp [hz]⟩) h
  refine ⟨c - 1 / 2, by linarith, ?_⟩
  intro δ hδ n
  obtain ⟨m, r, hm, hr, hrs⟩ := (exponent_lt_iff_rank zero_le_one zero_le_one hc).mp
    (show exponent F 1 1 c < 2 + δ by linarith)
  rw [side_one] at hr
  refine ⟨m ^ n, (side m c) ^ n, r ^ n, (Nat.lt_pow_self (by omega : 1 < m)).le, ?_, ?_, hr.pow n⟩
  · rw [show 1 / 2 + (c - 1 / 2) = c by ring]
    exact Nat.ceil_le.mp (side_pow (le_rfl : side m c ≤ _) n)
  · rw [Nat.cast_pow, Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity),
      mul_comm (n : ℝ), Real.rpow_mul_natCast (by positivity)]
    exact pow_le_pow_left₀ (by positivity) hrs.le _

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end
