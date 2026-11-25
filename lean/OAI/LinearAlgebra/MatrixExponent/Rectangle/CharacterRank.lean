import OAI.LinearAlgebra.MatrixExponent.Rectangle.Support
import OAI.LinearAlgebra.MatrixExponent.Upper.Character.DotsPower
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.FlatteningOrder

/-!
# From the character estimate to rectangular algorithms

Each pairing belongs to the two legs other than its named leg. Reading
the first two legs as inputs and the third as output gives a rank bound
on the formal product. Ceiling costs at most a factor of two per pairing.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Upper Upper.TensorClass

private def dots (i j k : ℕ) : TensorClass := dotX j * dotY i * dotZ k

private theorem dots_power (i j k t : ℕ) : dots (i ^ t) (j ^ t) (k ^ t) = (dots i j k) ^ t := by
  induction t with
  | zero => simp [dots]
  | succ t ih =>
    rw [pow_succ, pow_succ, pow_succ, pow_succ, ← ih]
    simp only [dots, ← dotX_mul, ← dotY_mul, ← dotZ_mul]
    exact (congrArg (· * _) (mul_mul_mul_comm _ _ _ _)).trans (mul_mul_mul_comm _ _ _ _)

open OAI.MatrixMultiplication.Foundation Upper.CoefficientTensor in
private theorem rank_of_dots {i j k r : ℕ} (h : dots i j k ≤ (r : TensorClass)) :
    RankLE Coeff i j k r := by
  have hr := TensorClass.rank_mono h
  rw [rank_natCast, dots, dotX, dotY, dotZ, ofTensor_mul, ofTensor_mul, rank_ofTensor] at hr
  obtain ⟨a, b, c, he⟩ := (CoefficientTensor.rank_le_iff _ _).mp hr
  refine ⟨fun l x => a l (((), x.1), x.2), fun l y => b l ((y.2, ()), y.1),
    fun l z => c l ((z.2, z.1), ()), ?_⟩
  intro x y z
  have hh := congrFun (congrFun (congrFun he (((), x.1), x.2)) ((y.2, ()), y.1)) ((z.2, z.1), ())
  refine hh.symm.trans ?_
  simp [Tensor.product, dotXCoeff, dotYCoeff, dotZCoeff, ite_and]
  grind

private theorem rounded_dot {n : ℕ} (hn : 0 < n) {a p : ℝ} (ha : 0 ≤ a)
    (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (side n a : ℝ) ^ p ≤ 2 * (n : ℝ) ^ (a * p) := by
  calc
    _ ≤ (2 * (n : ℝ) ^ a) ^ p :=
      Real.rpow_le_rpow (by positivity) (side_le hn ha) hp
    _ = (2 : ℝ) ^ p * (n : ℝ) ^ (a * p) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity)]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp'

private theorem price_dots (f : Character) {n : ℕ} (hn : 0 < n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (f (dots (side n a) (side n b) (side n c)) : ℝ) ≤
      8 * (n : ℝ) ^ (b * f.pX + a * f.pY + c * f.pZ) := by
  simp only [dots, Character.map_mul, NNReal.coe_mul]
  change f.dotXValue _ * f.dotYValue _ * f.dotZValue _ ≤ _
  rw [f.dotXValue_eq_rpow _ (side_pos hn b), f.dotYValue_eq_rpow _ (side_pos hn a),
    f.dotZValue_eq_rpow _ (side_pos hn c)]
  have hn₀ : 0 < (n : ℝ) := by positivity
  calc
    _ ≤ (2 * (n : ℝ) ^ (b * f.pX)) * (2 * (n : ℝ) ^ (a * f.pY)) *
        (2 * (n : ℝ) ^ (c * f.pZ)) := by
      gcongr
      · exact rounded_dot hn hb f.pX_nonneg f.pX_le_one
      · exact rounded_dot hn ha f.pY_nonneg f.pY_le_one
      · exact rounded_dot hn hc f.pZ_nonneg f.pZ_le_one
    _ = _ := by rw [Real.rpow_add hn₀, Real.rpow_add hn₀]; ring

theorem exponent_le_of_characters {a b c s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hs : 0 ≤ s)
    (h : ∀ f : Character, b * f.pX + a * f.pY + c * f.pZ ≤ s) :
    exponent Coeff a b c ≤ s := by
  by_contra! hlt
  obtain ⟨n, r, hn, hlo, hhi⟩ := price_gap hs hlt
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hr : 0 < (r : ℝ) := (by positivity : 0 ≤ 8 * (n : ℝ) ^ s).trans_lt hlo
  have hne : (r : TensorClass) ≠ 0 := by
    intro he
    have he' := (rank_eq_zero_iff _).mpr he
    rw [rank_natCast] at he'
    exact hr.ne' (by exact_mod_cast he')
  let M := dots (side n a) (side n b) (side n c)
  have hp (g : TensorClass →+* NNReal) (hg : Monotone g) : g M < g (r : TensorClass) := by
    let f : Character := ⟨g, hg⟩
    rw [map_natCast]
    apply NNReal.coe_lt_coe.mp
    calc
      (g M : ℝ) ≤ 8 * (n : ℝ) ^ (b * f.pX + a * f.pY + c * f.pZ) :=
        price_dots f (by omega) ha hb hc
      _ ≤ 8 * (n : ℝ) ^ s :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn₁ (h f)) (by norm_num)
      _ < (r : ℝ) := hlo
  obtain ⟨C, hC⟩ := Spectrum.strictComparison
    (fun _ _ _ h => add_mono h le_rfl) (fun _ _ _ h => mul_mono le_rfl h)
    TensorClass.zero_le (fun _ => one_le_of_ne_zero) (fun A => ⟨rank A, le_rank_natCast A⟩) hne hp
  obtain ⟨p, hp', hsave⟩ := absorb_overhead (D := C) hn hr hhi
  have hR : RankLE Coeff ((side n a) ^ p) ((side n b) ^ p) ((side n c) ^ p) (r ^ p * C) := by
    apply rank_of_dots
    rw [dots_power, Nat.cast_mul, Nat.cast_pow, mul_comm]
    exact hC p
  exact lt_irrefl _ (exponent_lt_of_rank ha hb hc hp'
    (hR.cut (side_pow le_rfl p) (side_pow le_rfl p) (side_pow le_rfl p)) hsave)

theorem coeff_discrete
    (h : ∀ (f : Character) (A B C : ℕ), 0 < A → 0 < B → 0 < C →
      4 * (f.pX * B * C + f.pY * A * C + f.pZ * A * B) ≤ ((A : ℝ) + B + C) ^ 2) :
    DiscreteBound Coeff := by
  intro A B C hA hB hC
  apply exponent_le_of_characters (by positivity) (by positivity) (by positivity) (by positivity)
  intro f
  linarith only [h f B C A hB hC hA]

end OAI.LinearAlgebra.MatrixExponent.Rectangle
