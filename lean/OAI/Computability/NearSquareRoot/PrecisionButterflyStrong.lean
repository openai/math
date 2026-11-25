import OAI.Computability.NearSquareRoot.PrecisionButterflyMatrix

/-! # Error of the final odd butterfly on a perturbed even-layer output -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication

private theorem roundBranch14 {k : ℕ} (sign : Bool) (x y c : Record k)
    (hx : ‖value k x‖ ≤ (2:ℝ)^(14*k)) (hy : ‖value k y‖ ≤ (2:ℝ)^(14*k))
    (hc : ‖value k c‖ ≤ 2) :
    ‖value k (normalizedBranch k sign x y c) -
      value k c * butterflySum sign (value k x) (value k y)‖ ≤ 1/(2:ℝ)^(70*k) := by
  let b := butterflySum sign (value k x) (value k y)
  have hb : ‖b‖ ≤ 2*(2:ℝ)^(14*k) := by
    have hs : ‖b‖ ≤ ‖value k x‖+‖value k y‖ := by
      cases sign
      · exact norm_add_le ..
      · exact norm_sub_le ..
    linarith
  have room : 4*(2:ℝ)^(14*k)*2^fractionBits k+2 < 2^componentBits k := by
    rw [fractionBits,componentBits,pow_succ,pow_add (2:ℝ) (96*k) 4]
    have mul : (2:ℝ)^(14*k)*2^(70*k)=2^(84*k) := by rw [←pow_add]; congr 1; omega
    have range : (2:ℝ)^(84*k)≤2^(96*k) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith only [mul,range,one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n := 96*k)]
  have hv : value k (butterflySum sign x y) = b := by
    apply butterflySum_value
    have := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ 2^fractionBits k)
    nlinarith only [this,room,mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) (14*k))
      (pow_nonneg (by norm_num : (0:ℝ)≤2) (fractionBits k))]
  have fit : ‖value k (butterflySum sign x y)*value k c‖ * (2:ℝ)^fractionBits k + 2 <
      2^componentBits k := by
    rw [norm_mul,hv]
    apply lt_of_le_of_lt _ room
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa only [mul_right_comm _ _ (2:ℝ), show (2:ℝ)*2=4 by norm_num] using
      mul_le_mul hb hc (norm_nonneg _) (by positivity)
  have e := Grid.confident (fractionBits k) (butterflySum sign x y) c fit
  change ‖value k (normalizedBranch k sign x y c) - value k (butterflySum sign x y)*value k c‖ ≤ _ at e
  rw [hv, mul_comm b] at e
  apply e.trans_eq
  rw [fractionBits, pow_succ]
  field_simp

/-- The shared scalar error is relative to the total norm of the exact
sum/difference array. Only fixed-point multiplication errors accumulate with
the square root of the number of output records. -/
theorem directWalshLayer_error55 {ι : Type*} [Fintype ι] {k : ℕ} (hk : 1≤k)
    (hcard : Fintype.card (ι × Bool) ≤ 2^k) (x : ι × Bool → Record k) (c : Record k)
    (hx : ‖recordArray x‖ ≤ (2:ℝ)^(14*k))
    (hc : ‖value k c - (SynchronizedPair.w:ℂ)‖ ≤ 1/(2:ℝ)^(70*k)) :
    ‖recordArray (fun j : ι × Bool => normalizedBranch k j.2 (x (j.1,false)) (x (j.1,true)) c) -
      (WithLp.toLp 2 (fun j : ι × Bool => (SynchronizedPair.w:ℂ) *
        butterflySum j.2 (value k (x (j.1,false))) (value k (x (j.1,true)))) :
          EuclideanSpace ℂ (ι × Bool))‖ ≤ 1/(2:ℝ)^(55*k) := by
  let b : EuclideanSpace ℂ (ι × Bool) := WithLp.toLp 2 (fun j =>
    butterflySum j.2 (value k (x (j.1,false))) (value k (x (j.1,true))))
  have root : 0 < Real.sqrt 2 := by positivity
  have inv : (Real.sqrt 2:ℂ)*(SynchronizedPair.w:ℂ)=1 := by
    unfold SynchronizedPair.w
    norm_cast
    exact mul_inv_cancel₀ root.ne'
  have eqb : b = (Real.sqrt 2:ℂ) • directWalsh ι (recordArray x) := by
    ext j
    change _ = (Real.sqrt 2:ℂ)*((SynchronizedPair.w:ℂ)*_)
    rw [← mul_assoc, inv, one_mul]
    rfl
  have bn : ‖b‖ ≤ (3/2)*(2:ℝ)^(14*k) := by
    rw [eqb, norm_smul, LinearIsometry.norm_map, Complex.norm_real, Real.norm_eq_abs, abs_of_pos root]
    apply mul_le_mul _ hx (norm_nonneg _) (by norm_num)
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have cs : ‖value k c‖ ≤ 2 := by
    have h := norm_le_norm_sub_add (value k c) (SynchronizedPair.w:ℂ)
    have hs : SynchronizedPair.w ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by norm_num))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by unfold SynchronizedPair.w; positivity)] at h
    linarith [(div_le_one (by positivity : (0:ℝ)<2^(70*k))).mpr (one_le_pow₀ (by norm_num))]
  have entry (j : ι × Bool) : ‖value k (x j)‖ ≤ (2:ℝ)^(14*k) :=
    (PiLp.norm_apply_le (recordArray x) j).trans hx
  apply (phaseLayer_error_le (fun _ : ι × Bool => (SynchronizedPair.w:ℂ)) (fun _ => value k c) b _
    (by positivity) bn (fun _ => hc) (fun j => roundBranch14 j.2 _ _ c (entry _) (entry _) cs)).trans
  have hd : Real.sqrt (Fintype.card (ι × Bool)) ≤ (2:ℝ)^k := by
    have hN : (Fintype.card (ι × Bool):ℝ) ≤ (2:ℝ)^k := by exact_mod_cast hcard
    exact (Real.sqrt_le_sqrt hN).trans (Real.sqrt_le_self_iff.mpr (.inr (one_le_pow₀ (by norm_num))))
  have dim : (2:ℝ)^k*2 ≤ 2^(14*k) := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have margin : (3/2)*(2:ℝ)^(14*k) + Real.sqrt (Fintype.card (ι × Bool)) ≤ 2^(15*k) := by
    apply le_trans _ (pow_le_pow_right₀ (a := (2:ℝ)) (by norm_num) (show 14*k+1≤15*k by omega))
    rw [pow_succ]
    linarith
  apply (mul_le_mul_of_nonneg_left margin (by positivity)).trans_eq
  rw [show 70*k = 55*k+15*k by omega, pow_add]
  field_simp

/-- Matrix form for the concrete reciprocal-square-root word emitted by
the direct odd-bit setup routine. -/
theorem record_butterfly_error55 (ι : Type*) [Fintype ι] [DecidableEq ι] {k : ℕ} (hk : 1≤k)
    (hcard : Fintype.card (ι × Bool) ≤ 2^k) (x : ι × Bool → Record k)
    (hx : ‖recordArray x‖ ≤ (2:ℝ)^(14*k)) :
    ‖recordArray (fun j : ι × Bool => normalizedBranch k j.2
        (x (j.1,false)) (x (j.1,true)) (butterflyCoefficient k)) -
      SynchronizedPadding.matrixIsometry _ (butterflyMatrix_unitary ι) (recordArray x)‖ ≤
      1/(2:ℝ)^(55*k) := by
  rw [← directWalsh_eq_matrix]
  exact directWalshLayer_error55 hk hcard x _ hx (butterflyCoefficient_error k)

end FixedPoint

end NearSquareRoot
end Computability
end OAI
