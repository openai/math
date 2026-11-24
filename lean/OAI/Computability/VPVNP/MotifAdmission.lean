import OAI.Computability.VPVNP.MotifWidths
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size

/-!
# Integer admission tests for a fixed rational wire motif

Theorem 6.1 of *VP and VNP differ over every field* selects a demand grid
point and a block repetition count from the input widths. The outer supply
index is admitted by testing a rational quadratic bound. Clearing the fixed
mass denominators gives integer algorithms for all three operations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifAdmission

open MotifGrid

variable {I : Type*} [Fintype I]

/-- Common denominator of the reciprocal edge masses. -/
def denominator (p : I → ℚ) : ℕ := ∏ i, (p i)⁻¹.den

/-- The positive integer coefficient of one squared width after clearing denominators. -/
def weight (p : I → ℚ) (i : I) : ℕ :=
  (p i)⁻¹.num.natAbs * (denominator p / (p i)⁻¹.den)

/-- Integral numerator of the squared width norm. -/
def energy (p : I → ℚ) (b : I → ℕ) : ℕ := ∑ i, weight p i * b i ^ 2

theorem denominator_pos (p : I → ℚ) : 0 < denominator p :=
  Finset.prod_pos fun i _ => (p i)⁻¹.den_pos

private theorem numerator_cast (r : ℚ) (hr : 0 ≤ r) :
    (r.num.natAbs : ℝ) = (r.num : ℝ) := by
  rw [Nat.cast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hr)]

private theorem rational_cast (r : ℚ) (hr : 0 ≤ r) :
    (r : ℝ) = (r.num.natAbs : ℝ) / r.den := by
  rw [Rat.cast_def, numerator_cast r hr]

private theorem weight_cast (p : I → ℚ) (hp : ∀ i, 0 < p i) (i : I) :
    (weight p i : ℝ) = (denominator p : ℝ) / (p i : ℝ) := by
  let r := (p i)⁻¹
  have hden : r.den ∣ denominator p :=
    Finset.dvd_prod_of_mem (fun j => (p j)⁻¹.den) (Finset.mem_univ i)
  have hclear : ((denominator p / r.den : ℕ) : ℝ) * r.den = denominator p := by
    exact_mod_cast Nat.div_mul_cancel hden
  have hr : 0 ≤ r := (inv_pos.mpr (hp i)).le
  have hrpos : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.den_pos
  change (↑(r.num.natAbs * (denominator p / r.den)) : ℝ) = _
  calc
    _ = (r : ℝ) * denominator p := by
      rw [rational_cast r hr, ← hclear, Nat.cast_mul]
      field_simp
    _ = _ := by simp [r, div_eq_mul_inv, mul_comm]

/-- The integral energy with its fixed denominator recovers the real norm. -/
theorem norm_sq_eq (p : I → ℚ) (hp : ∀ i, 0 < p i) (b : I → ℕ) :
    widthNorm (realWidths p) (fun i => (b i : ℝ)) ^ 2 = (energy p b : ℝ) / denominator p := by
  rw [norm_sq (realWidths p) _ (fun i => Rat.cast_pos.mpr (hp i))]
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (denominator_pos p).ne')).mpr
  simp only [energy, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Finset.sum_mul, realWidths]
  exact Finset.sum_congr rfl fun i _ => by rw [weight_cast p hp i]; ring

/-- Consume one base-four digit per recursive step. The result with enough
digits is the binary integer square root. -/
def sqrtDigits : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n =>
    let a := 2 * sqrtDigits k (n / 4)
    if (a + 1) ^ 2 ≤ n then a + 1 else a

theorem sqrtDigits_eq (k n : ℕ) (hn : n < 4 ^ k) : sqrtDigits k n = n.sqrt := by
  induction k generalizing n with
  | zero =>
    have h0 : n = 0 := Nat.lt_one_iff.mp hn
    simp [h0, sqrtDigits]
  | succ k ih =>
    have hd : n / 4 < 4 ^ k :=
      (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [pow_succ] using hn)
    let r := (n / 4).sqrt
    have hlo : (2 * r) ^ 2 ≤ n := by
      have h := (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mp (Nat.sqrt_le' (n / 4))
      calc
        (2 * r) ^ 2 = r ^ 2 * 4 := by ring
        _ ≤ n := h
    have hhi : n < (2 * r + 1 + 1) ^ 2 := by
      have h := (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mp (Nat.lt_succ_sqrt' (n / 4))
      calc
        n < (r + 1) ^ 2 * 4 := h
        _ = (2 * r + 1 + 1) ^ 2 := by ring
    simp only [sqrtDigits, ih _ hd]
    change (if (2 * r + 1) ^ 2 ≤ n then 2 * r + 1 else 2 * r) = n.sqrt
    split
    · rename_i h
      exact Nat.eq_sqrt'.mpr ⟨h, hhi⟩
    · rename_i h
      exact Nat.eq_sqrt'.mpr ⟨hlo, Nat.lt_of_not_ge h⟩

/-- Executable floor square root of a rational energy. Binary input length
bounds the number of recursive steps. -/
def floorRoot (n d : ℕ) : ℕ :=
  let m := n / d
  sqrtDigits m.size m

theorem floorRoot_eq (n d : ℕ) : floorRoot n d = (n / d).sqrt := by
  apply sqrtDigits_eq
  exact (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_left (by decide : 2 ≤ 4) _)

theorem sqrtDigit_operand_le (n : ℕ) : (2 * (n / 4).sqrt + 1) ^ 2 ≤ 4 * (n + 1) := by
  let r := (n / 4).sqrt
  have hlo : r ^ 2 * 4 ≤ n :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mp (Nat.sqrt_le' (n / 4))
  have hr : r ≤ r ^ 2 := Nat.le_self_pow (by decide) r
  change (2 * r + 1) ^ 2 ≤ 4 * (n + 1)
  nlinarith only [hlo, hr, Nat.zero_le (r ^ 2)]

/-- Ceiling of the square root of an unsigned fraction. At a perfect square
the decrement prevents a spurious additional copy. -/
def ceilRoot (n d : ℕ) : ℕ :=
  if n = 0 then 0 else floorRoot (n - 1) d + 1

theorem ceilRoot_le_iff (n d k : ℕ) (hd : 0 < d) :
    ceilRoot n d ≤ k ↔ n ≤ k ^ 2 * d := by
  by_cases hn : n = 0
  · simp [hn, ceilRoot]
  · rw [ceilRoot, ite_eq_right hn, floorRoot_eq, Nat.succ_le_iff, Nat.sqrt_lt',
      Nat.div_lt_iff_lt_mul hd]
    omega

/-- Executable number of block repetitions. -/
def copies (p : I → ℚ) (b : I → ℕ) (L : ℕ) : ℕ :=
  ceilRoot (energy p b) (L ^ 2 * denominator p)

/-- The integer calculation gives the ceiling used in the real width estimate. -/
theorem copies_eq (p : I → ℚ) (hp : ∀ i, 0 < p i) (b : I → ℕ) (L : ℕ) (hL : 0 < L) :
    copies p b L = MotifWidths.copies (widthNorm (realWidths p) (fun i => b i)) L := by
  apply eq_of_forall_ge_iff
  intro k
  have hn : 0 ≤ widthNorm (realWidths p) (fun i => (b i : ℝ)) := Real.sqrt_nonneg _
  rw [copies, ceilRoot_le_iff _ _ _ (Nat.mul_pos (pow_pos hL _) (denominator_pos p)),
    MotifWidths.copies, Nat.ceil_le, div_le_iff₀ (Nat.cast_pos.mpr hL),
    ← sq_le_sq₀ hn (mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg L)),
    norm_sq_eq p hp b, div_le_iff₀ (Nat.cast_pos.mpr (denominator_pos p)), mul_pow, mul_assoc]
  norm_cast

/-- Test the two integer sides of the payload constraint. -/
def admit (q : I → ℚ) (v : I → ℕ) (u L : ℕ) (R : ℚ) : Bool :=
  decide (energy q v * R.den ^ 2 ≤ (u * L * R.num.natAbs) ^ 2 * denominator q)

theorem admit_eq_true_iff (q : I → ℚ) (hq : ∀ i, 0 < q i) (v : I → ℕ)
    (u L : ℕ) (R : ℚ) (hR : 0 ≤ R) :
    admit q v u L R = true ↔
      widthNorm (realWidths q) (fun i => v i) ≤ (u : ℝ) * L * (R : ℝ) := by
  have hn : 0 ≤ widthNorm (realWidths q) (fun i => (v i : ℝ)) := Real.sqrt_nonneg _
  have hRden : (0 : ℝ) < R.den := Nat.cast_pos.mpr R.den_pos
  rw [admit, decide_eq_true_eq, rational_cast R hR, ← mul_div_assoc, le_div_iff₀ hRden,
    ← sq_le_sq₀ (mul_nonneg hn hRden.le) (show 0 ≤ (u : ℝ) * L * R.num.natAbs by positivity),
    mul_pow (widthNorm _ _), norm_sq_eq q hq v, div_mul_eq_mul_div,
    div_le_iff₀ (Nat.cast_pos.mpr (denominator_pos q))]
  norm_cast

/-- Check that a nonnegative rational grid point dominates the normalized
demand in one coordinate, without division by the demand norm. -/
def coversCoordinate (p : I → ℚ) (b : I → ℕ) (i : I) (r : ℚ) : Bool :=
  decide (0 ≤ r ∧
    (b i * r.den) ^ 2 * denominator p ≤ energy p b * r.num.natAbs ^ 2)

theorem coversCoordinate_eq_true_iff (p : I → ℚ) (hp : ∀ i, 0 < p i)
    (b : I → ℕ) (i : I) (r : ℚ) :
    coversCoordinate p b i r = true ↔ 0 ≤ r ∧
      (b i : ℝ) ≤ widthNorm (realWidths p) (fun j => b j) * (r : ℝ) := by
  rw [coversCoordinate, decide_eq_true_eq, and_congr_right_iff]
  intro hr
  have hrd : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.den_pos
  have hn : 0 ≤ widthNorm (realWidths p) (fun j => (b j : ℝ)) := Real.sqrt_nonneg _
  rw [rational_cast r hr, ← mul_div_assoc, le_div_iff₀ hrd,
    ← sq_le_sq₀ (mul_nonneg (Nat.cast_nonneg _) hrd.le) (mul_nonneg hn (Nat.cast_nonneg _)),
    mul_pow (widthNorm _ _), norm_sq_eq p hp b, div_mul_eq_mul_div,
    le_div_iff₀ (Nat.cast_pos.mpr (denominator_pos p))]
  norm_cast

/-- Choose the first covering point in a fixed ordering of the finite demand grid. -/
def selectGrid (p : I → ℚ) (b : I → ℕ) (table : List (I → ℚ)) : Option (I → ℚ) :=
  table.find? (fun z => decide (∀ i, coversCoordinate p b i (z i) = true))

theorem selectGrid_spec (p : I → ℚ) (hp : ∀ i, 0 < p i) (b : I → ℕ)
    {table : List (I → ℚ)} {z : I → ℚ} (h : selectGrid p b table = some z) :
    z ∈ table ∧ ∀ i, 0 ≤ z i ∧
      (b i : ℝ) ≤ widthNorm (realWidths p) (fun j => b j) * (z i : ℝ) := by
  refine ⟨List.mem_of_find?_eq_some h, fun i => (coversCoordinate_eq_true_iff p hp b i _).mp ?_⟩
  have hz := List.find?_some (p := fun w : I → ℚ =>
    decide (∀ j, coversCoordinate p b j (w j) = true)) h
  exact (of_decide_eq_true hz) i

/-- The strict demand grids have a covering entry, including at zero demand
where each coordinate of the demand vanishes. The choice depends only on the
ordered table, masses, and input widths. -/
theorem selectGrid_exists {S : Type*} [Fintype S] (p : I → ℚ) (hp : ∀ i, 0 < p i)
    {q : S → ℝ} {H R : ℝ} (G : StrictGrids (realWidths p) q H R)
    (b : I → ℕ) (table : List (I → ℚ)) (htable : ∀ z ∈ G.demands, z ∈ table) :
    ∃ z, selectGrid p b table = some z := by
  let N := widthNorm (realWidths p) (fun i => (b i : ℝ))
  have hn : 0 ≤ N := Real.sqrt_nonneg _
  let x := fun i => N⁻¹ * (b i : ℝ)
  have hx i : 0 ≤ x i := mul_nonneg (inv_nonneg.mpr hn) (Nat.cast_nonneg _)
  have hnorm : widthNorm (realWidths p) x ≤ 1 := by
    rw [show x = (fun i => N⁻¹ * (b i : ℝ)) from rfl, widthNorm_scale _ _ (inv_nonneg.mpr hn)]
    change N⁻¹ * N ≤ 1
    rcases eq_or_ne N 0 with he | he <;> simp [he]
  obtain ⟨z, hz, hcov⟩ := G.cover x hx hnorm
  apply Option.isSome_iff_exists.mp
  apply List.find?_isSome.mpr
  refine ⟨z, htable z hz, decide_eq_true ?_⟩
  intro i
  refine (coversCoordinate_eq_true_iff p hp b i _).mpr
    ⟨Rat.cast_nonneg.mp ((hx i).trans (hcov i).1), ?_⟩
  change (b i : ℝ) ≤ N * (z i : ℝ)
  rcases hn.eq_or_lt with h0 | hpos
  · have h := coordinate_le (realWidths p) (fun j => (b j : ℝ))
      (fun j => Rat.cast_pos.mpr (hp j)) i
    change (b i : ℝ) ≤ _ * N at h
    simpa [← h0] using h
  · have h := mul_le_mul_of_nonneg_left (hcov i).1 hn
    dsimp only [x] at h
    rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at h

/-- Every variable energy accumulator, including intermediate partial sums
of its nonnegative summands, has a fixed quadratic magnitude bound. -/
theorem energy_le (p : I → ℚ) (b : I → ℕ) (M : ℕ) (hb : ∀ i, b i ≤ M) :
    energy p b ≤ (∑ i, weight p i) * M ^ 2 := by
  rw [energy, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hb i) 2)

/-- A fixed coefficient bounds the repetition count linearly in the input width. -/
theorem copies_le (p : I → ℚ) (b : I → ℕ) (L M : ℕ) (hL : 0 < L)
    (hb : ∀ i, b i ≤ M) : copies p b L ≤ ((∑ i, weight p i) + 1) * (M + 1) := by
  let W := ∑ i, weight p i
  apply (ceilRoot_le_iff _ _ _ (Nat.mul_pos (pow_pos hL _) (denominator_pos p))).mpr
  have hW : W ≤ (W + 1) ^ 2 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  calc
    energy p b ≤ W * M ^ 2 := energy_le p b M hb
    _ ≤ (W + 1) ^ 2 * (M + 1) ^ 2 :=
      Nat.mul_le_mul hW (Nat.pow_le_pow_left (Nat.le_succ _) 2)
    _ = ((W + 1) * (M + 1)) ^ 2 := (mul_pow _ _ _).symm
    _ ≤ _ := Nat.le_mul_of_pos_right _ (Nat.mul_pos (pow_pos hL _) (denominator_pos p))

/-- A finite search box containing every admitted outer payload. -/
def payloadCap (q : I → ℚ) (u L : ℕ) (R : ℚ) : ℕ :=
  u * L * R.num.natAbs * denominator q

theorem payload_le_cap (q : I → ℚ) (hq : ∀ i, 0 < q i) (v : I → ℕ)
    (u L : ℕ) (R : ℚ) (hv : admit q v u L R = true) (i : I) :
    v i ≤ payloadCap q u L R := by
  have hwreal : (0 : ℝ) < weight q i := by
    rw [weight_cast q hq i]
    exact div_pos (Nat.cast_pos.mpr (denominator_pos q)) (Rat.cast_pos.mpr (hq i))
  have hw : 0 < weight q i := Nat.cast_pos.mp hwreal
  have he : v i ^ 2 ≤ energy q v :=
    (Nat.le_mul_of_pos_left _ hw).trans
      (Finset.single_le_sum (f := fun j => weight q j * v j ^ 2) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i))
  apply (Nat.pow_le_pow_iff_left (n := 2) (by decide)).mp
  rw [payloadCap, mul_pow]
  exact (he.trans (Nat.le_mul_of_pos_right _ (pow_pos R.den_pos 2))).trans
    ((of_decide_eq_true hv).trans (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) _)))

/-- Explicit quadratic bounds on both integers compared by the payload test
on a linearly sized candidate box. -/
theorem admit_operands_le (q : I → ℚ) (v : I → ℕ) (u L : ℕ) (R : ℚ) (K M : ℕ)
    (hu : u ≤ K * (M + 1)) (hv : ∀ i, v i ≤ K * (M + 1)) :
    energy q v * R.den ^ 2 ≤ ((∑ i, weight q i) * K ^ 2 * R.den ^ 2) * (M + 1) ^ 2 ∧
      (u * L * R.num.natAbs) ^ 2 * denominator q ≤
        ((K * L * R.num.natAbs) ^ 2 * denominator q) * (M + 1) ^ 2 := by
  constructor
  · apply (Nat.mul_le_mul_right (R.den ^ 2) (energy_le q v _ hv)).trans_eq
    ring
  · have h := Nat.mul_le_mul_right (denominator q) <|
      Nat.pow_le_pow_left (Nat.mul_le_mul_right R.num.natAbs (Nat.mul_le_mul_right L hu)) 2
    exact h.trans_eq (by ring)

/-- Quadratic bounds for the integer comparisons used to select a grid point.
Both coefficients are fixed for a fixed grid table. -/
theorem grid_operands_le (p : I → ℚ) (b : I → ℕ) (M : ℕ) (hb : ∀ i, b i ≤ M)
    (i : I) (r : ℚ) :
    (b i * r.den) ^ 2 * denominator p ≤ (r.den ^ 2 * denominator p) * (M + 1) ^ 2 ∧
      energy p b * r.num.natAbs ^ 2 ≤
        ((∑ j, weight p j) * r.num.natAbs ^ 2) * (M + 1) ^ 2 := by
  have hb' j : b j ≤ M + 1 := (hb j).trans (Nat.le_succ M)
  constructor
  · apply (Nat.mul_le_mul_right (denominator p) (Nat.pow_le_pow_left
      (Nat.mul_le_mul_right r.den (hb' i)) 2)).trans_eq
    ring
  · apply (Nat.mul_le_mul_right (r.num.natAbs ^ 2) (energy_le p b _ hb')).trans_eq
    ring

/-- Quadratically bounded operands have bit length at most a constant plus
twice the binary logarithm of the input width. -/
theorem operand_bits_le (a K M : ℕ) (ha : a ≤ K * (M + 1) ^ 2) :
    a.size ≤ K.size + 2 * Nat.clog 2 (M + 1) := by
  apply Nat.size_le.mpr
  rw [pow_add, Nat.mul_comm 2, pow_mul]
  apply ha.trans_lt
  exact mul_lt_mul_of_lt_of_le_of_pos_of_nonneg (Nat.lt_size_self K)
    (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) 2) (by positivity) (by positivity)

/-- The finite payload search box is linear in the original maximum width. -/
theorem payloadCap_le {J : Type*} [Fintype J] (p : I → ℚ) (q : J → ℚ)
    (b : I → ℕ) (L M : ℕ) (R : ℚ) (hL : 0 < L) (hb : ∀ i, b i ≤ M) :
    payloadCap q (copies p b L) L R ≤
      (((∑ i, weight p i) + 1) * L * R.num.natAbs * denominator q) * (M + 1) := by
  apply (Nat.mul_le_mul_right (denominator q) (Nat.mul_le_mul_right R.num.natAbs
    (Nat.mul_le_mul_right L (copies_le p b L M hL hb)))).trans_eq
  ring

/-- The recursion depth in the executable ceiling test is bounded in terms
of the original maximum width and the fixed mass coefficients. -/
theorem copies_root_steps_le (p : I → ℚ) (b : I → ℕ) (L M : ℕ) (hb : ∀ i, b i ≤ M) :
    ((energy p b - 1) / (L ^ 2 * denominator p)).size ≤
      (∑ i, weight p i).size + 2 * Nat.clog 2 (M + 1) := by
  apply operand_bits_le
  exact (Nat.div_le_self _ _).trans <| (Nat.sub_le _ _).trans <|
    energy_le p b (M + 1) (fun i => (hb i).trans (Nat.le_succ M))

end MotifAdmission

end VPVNP
end Computability
end OAI
