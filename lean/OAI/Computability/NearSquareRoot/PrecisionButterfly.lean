import OAI.Computability.NearSquareRoot.PrecisionRecordArithmetic
import OAI.Computability.NearSquareRoot.SynchronizedPair

/-! # Finite-precision direct Walsh butterfly

The odd selected address bit is treated by addition and subtraction on paired
records, followed by multiplication by a dyadic approximation to `1 / √2`.
The guard on the input is the full allowance at an internal layer boundary.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication

/-- The two branches of a butterfly, before the common normalization. -/
def butterflySum {R : Type*} [AddGroup R] (negative : Bool) (x y : R) : R :=
  if negative then x - y else x + y

private theorem norm_butterflySum_le {R : Type*} [SeminormedAddCommGroup R]
    (negative : Bool) (x y : R) : ‖butterflySum negative x y‖ ≤ ‖x‖+‖y‖ := by
  cases negative
  · exact norm_add_le ..
  · exact norm_sub_le ..

/-- Signed record addition agrees exactly with complex addition or subtraction
when the scaled exact answer lies strictly inside the signed representation. -/
theorem butterflySum_value {p w : ℕ} (negative : Bool) (x y : Dusk.Grain w)
    (h : ‖butterflySum negative (Grid.meaning p w x) (Grid.meaning p w y)‖ *
      (2 : ℝ)^p < 2^w) :
    Grid.meaning p w (butterflySum negative x y) =
      butterflySum negative (Grid.meaning p w x) (Grid.meaning p w y) := by
  let c := butterflySum negative (Grid.aspect x) (Grid.aspect y)
  have hval : Grid.toC c / (2 : ℂ)^p =
      butterflySum negative (Grid.meaning p w x) (Grid.meaning p w y) := by
    cases negative <;> simp [c, butterflySum, Grid.meaning, sub_div, add_div]
  have hrep : Grid.wrapMap w c = butterflySum negative x y := by
    cases negative <;> simp [c, butterflySum]
  rw [← hval, ← hrep, Grid.meaning, Grid.recovers c]
  apply Grid.short _ (Grid.into _)
  rw [← hval, norm_div, norm_pow, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num,
    div_mul_cancel₀ _ (by positivity)] at h
  exact h

/-- Encoded scalar multiplication after exact preparation of one branch. -/
def normalizedBranch (k : ℕ) (negative : Bool) (x y c : Record k) : Record k :=
  multiply k (butterflySum negative x y) c

private theorem butterflyHeadroom (k : ℕ) :
    (4 * (2 : ℝ)^(13*k)) * 2 ^ fractionBits k + 2 < 2 ^ componentBits k := by
  have h : (2 : ℝ)^(83*k) ≤ 2^(96*k) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h₁ : (1 : ℝ) ≤ 2^(96*k) := one_le_pow₀ (by norm_num)
  rw [fractionBits, componentBits, pow_succ, pow_add (2 : ℝ) (96*k) 4]
  have hp : (2 : ℝ)^(13*k) * 2^(70*k) = 2^(83*k) := by
    rw [← pow_add, show 13*k+70*k = 83*k by omega]
  nlinarith only [hp, h, h₁]

private theorem butterflyScale_le_one : |SynchronizedPair.w| ≤ 1 := by
  unfold SynchronizedPair.w
  rw [abs_of_nonneg (by positivity), inv_le_one₀ (by positivity)]
  exact Real.one_le_sqrt.mpr (by norm_num)

/-- Absolute error of each represented branch, including rounding the signed
complex product and approximating its shared scalar. -/
theorem normalizedBranch_error {k : ℕ} (negative : Bool) (x y c : Record k)
    (hx : ‖value k x‖ ≤ (2 : ℝ)^(13*k)) (hy : ‖value k y‖ ≤ (2 : ℝ)^(13*k))
    (hc : ‖value k c - (SynchronizedPair.w : ℂ)‖ ≤ 1 / (2 : ℝ)^(70*k)) :
    ‖value k (normalizedBranch k negative x y c) -
        (SynchronizedPair.w : ℂ) * butterflySum negative (value k x) (value k y)‖ ≤
      (1 + 2 * (2 : ℝ)^(13*k)) / (2 : ℝ)^(70*k) := by
  let b := butterflySum negative (value k x) (value k y)
  have hb : ‖b‖ ≤ 2 * (2 : ℝ)^(13*k) := (norm_butterflySum_le ..).trans (by linarith)
  have hroom := butterflyHeadroom k
  have hbranch : value k (butterflySum negative x y) = b := by
    apply butterflySum_value
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hb.trans (by linarith [pow_pos (by norm_num : (0:ℝ)<2) (13*k)])) (by positivity))
      ((lt_add_of_pos_right _ (by norm_num : (0:ℝ)<2)).trans hroom)
  have hc₁ : ‖value k c‖ ≤ 2 := by
    have hu := norm_le_norm_sub_add (value k c) (SynchronizedPair.w : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at hu
    linarith [butterflyScale_le_one, (div_le_one (by positivity : (0:ℝ)<2^(70*k))).mpr
      (one_le_pow₀ (by norm_num))]
  have fit : ‖value k (butterflySum negative x y) * value k c‖ *
      (2 : ℝ)^fractionBits k + 2 < 2^componentBits k := by
    rw [norm_mul, hbranch]
    apply lt_of_le_of_lt _ hroom
    have h := mul_le_mul hb hc₁ (norm_nonneg _) (by positivity)
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have he := Grid.confident (fractionBits k) (butterflySum negative x y) c fit
  change ‖value k (normalizedBranch k negative x y c) -
      value k (butterflySum negative x y)*value k c‖ ≤ 2/(2 : ℝ)^fractionBits k at he
  rw [hbranch] at he
  have hround : 2 / (2 : ℝ)^fractionBits k = 1/2^(70*k) := by
    rw [fractionBits, pow_succ]; field_simp
  rw [hround] at he
  have hs : ‖b * value k c - (SynchronizedPair.w : ℂ)*b‖ ≤
      (2 * (2 : ℝ)^(13*k)) * (1 / (2 : ℝ)^(70*k)) := by
    rw [mul_comm (SynchronizedPair.w : ℂ), ← mul_sub, norm_mul]
    exact mul_le_mul hb hc (norm_nonneg _) (by positivity)
  apply (norm_sub_le_norm_sub_add_norm_sub _ (b * value k c) _).trans
  exact (add_le_add he hs).trans_eq (by ring)

/-- The complete adjacent-pair pass meets the Walsh layer accuracy budget on
the padded array. The two arrays need no assumptions on leading or padding
records. The sign of an output is encoded by its side of the pair. -/
theorem directWalshLayer_error {ι : Type*} [Fintype ι] {k : ℕ} (hk : 1 ≤ k)
    (hcard : Fintype.card (ι × Bool) ≤ 2^k) (x : ι × Bool → Record k) (c : Record k)
    (hx : ‖recordArray x‖ ≤ (2 : ℝ)^(13*k))
    (hc : ‖value k c - (SynchronizedPair.w : ℂ)‖ ≤ 1 / (2 : ℝ)^(70*k)) :
    ‖recordArray (fun j : ι × Bool => normalizedBranch k j.2 (x (j.1,false)) (x (j.1,true)) c) -
      (WithLp.toLp 2 (fun j : ι × Bool => (SynchronizedPair.w : ℂ) *
        butterflySum j.2 (value k (x (j.1,false))) (value k (x (j.1,true)))) :
        EuclideanSpace ℂ (ι × Bool))‖ ≤ 1 / (2 : ℝ)^(50*k) := by
  have hnorm (j : ι × Bool) : ‖value k (x j)‖ ≤ (2 : ℝ)^(13*k) :=
    (PiLp.norm_apply_le (recordArray x) j).trans hx
  apply (euclidean_norm_le_of_coordinates _ (by positivity) (fun j =>
    normalizedBranch_error j.2 _ _ c (hnorm _) (hnorm _) hc)).trans
  have hd : Real.sqrt (Fintype.card (ι × Bool)) ≤ (2 : ℝ)^k := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hN : (Fintype.card (ι × Bool) : ℝ) ≤ 2^k := by exact_mod_cast hcard
    have h₁ : (1 : ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
    exact hN.trans (by nlinarith)
  have h₁ : (1 : ℝ) ≤ 2^(13*k) := one_le_pow₀ (by norm_num)
  calc
    _ ≤ (2 : ℝ)^k * ((4 * 2^(13*k)) / 2^(70*k)) := by gcongr; linarith
    _ = (2 : ℝ)^(14*k+2) / 2^(70*k) := by
      rw [pow_add (2 : ℝ) (14*k) 2, show 14*k = k+13*k by omega, pow_add]; ring
    _ ≤ 1 / (2 : ℝ)^(50*k) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), ← pow_add, one_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)

end FixedPoint

end NearSquareRoot
end Computability
end OAI
