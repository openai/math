import OAI.Computability.IntegerMultiplication.Fourier.Window
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier
open Finset Real

theorem coef_pos {D i} (hi : i∈rad D) : 0<coef D i := by
  rw [coef, ite_eq_left hi]
  apply div_pos _ (by positivity)
  exact_mod_cast Nat.choose_pos (k := unoff D i) (n := 2*D)
    (by rw [unoff]; have e := mem_rad.mp hi; omega)

@[simp] theorem coef_nonneg (D i) : 0≤coef D i := by unfold coef; split <;> positivity

theorem coef_neg (D i) : coef D (-i)=coef D i := by
  unfold coef
  split
  · next e =>
    have h : i∈rad D := by simp at e ⊢; omega
    rw [ite_eq_left h]
    congr 2
    have hh := mem_rad.mp h
    rw [show unoff D (-i)=2*D-unoff D i by unfold unoff; omega,
      Nat.choose_symm (by unfold unoff; omega)]
  · next e =>
    rw [ite_eq_right (by simp at e ⊢; omega)]

theorem coef_abs (D i) : coef D (i.natAbs : ℤ) = coef D i := by
  rw [Int.natCast_natAbs]
  rcases le_or_gt 0 i with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, coef_neg]

private theorem coef_zero' (D : ℕ) :
    coef D 0 = (((2*D).choose D:ℕ):ℝ)/4^D := by simp [coef,unoff]

theorem coef_le_center (D i) : coef D i ≤ coef D 0 := by
  rw [coef_zero']
  unfold coef
  split
  · gcongr
    simpa using Nat.choose_le_middle (unoff D i) (2*D)
  · positivity

theorem coef_sum (D : ℕ) : ∑ i ∈ rad D, coef D i = 1 := by
  have h := (window_phase D 1 0).symm
  have e : ∑ i ∈ rad D, ((coef D i : ℝ):ℂ)=1 := by simpa [phase,window] using h
  apply Complex.ofReal_injective
  push_cast
  exact e

@[simp]
theorem rad_card (D : ℕ) : (rad D).card = 2*D+1 := by rw [rad,Int.card_Icc]; omega

theorem center_lower (D : ℕ) : 1 / (2 * (D:ℝ)+1) ≤ coef D 0 := by
  have h : ∑ i ∈ rad D, coef D i ≤ ∑ _i ∈ rad D, coef D 0 :=
    sum_le_sum fun i _ => coef_le_center D i
  simp only [coef_sum, sum_const,rad_card,nsmul_eq_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at h
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- The ratio between consecutive coefficients on the right side, with scale
cancellation already done. -/
theorem coef_step {D i : ℕ} (h : i < D) :
    coef D (↑(i+1:ℕ)) =
    coef D (↑(i:ℕ)) * (1-(2*i+1:ℝ)/(D+i+1)) := by
  have he := Nat.choose_succ_right_eq (2*D) (D+i)
  have e : ((((2*D).choose (D+i+1)):ℕ):ℝ)*(D+i+1) =
    ((((2*D).choose (D+i)):ℕ):ℝ)*(D-i) := by
    have h' : (((2*D).choose (D+i+1)*(D+i+1):ℕ):ℝ)=(((2*D).choose (D+i)*(2*D-(D+i)):ℕ):ℝ) := congrArg Nat.cast he
    rw [show 2*D-(D+i)=D-i by omega] at h'
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,Nat.cast_sub (by omega : i≤D)] at h'
    exact h'
  have u : (↑i : ℤ)∈rad D := by simp; omega
  have v : (↑(i+1:ℕ) : ℤ)∈rad D := by simp; omega
  have hb (j : ℕ) : unoff D (j:ℤ)=D+j := by unfold unoff; omega
  rw [coef,coef,ite_eq_left u,ite_eq_left v,hb,hb,← Nat.add_assoc] -- grouping?
  field_simp
  linarith

/-- The upper ratio bound. -/
private theorem step_up (D i : ℕ) (h : i < D) :
    coef D (↑(i+1:ℕ)) ≤
    coef D (i:ℤ)* Real.exp (-(2*i+1:ℝ)/(2*D)) := by
  rw [coef_step h]
  refine mul_le_mul_of_nonneg_left ?_ (coef_nonneg ..)
  have h₁ : (2*i+1:ℝ)/(2*D) ≤ (2*i+1:ℝ)/(D+i+1) := by
    gcongr; first | positivity |
      (have e : (i:ℝ)+1≤D := by exact_mod_cast Nat.succ_le_of_lt h
       linarith)
  have h₂ := Real.add_one_le_exp (-(2*i+1:ℝ)/(2*D))
  simp only [neg_div] at h₂ ⊢
  linarith

theorem coef_right_bound (D a b : ℕ) (ha : a ≤ b) :
    coef D (b:ℤ) ≤
    coef D (a:ℤ)*Real.exp (-((b:ℝ)^2-(a:ℝ)^2)/(2*D)) := by
  by_cases hb : D < b
  · conv_lhs => unfold coef; rw [ite_eq_right (by simp; omega)]
    exact mul_nonneg (coef_nonneg ..) (Real.exp_pos _).le
  push Not at hb
  induction b with
  | zero =>
    have e : a=0 := by omega
    subst a; simp
  | succ b ih =>
    by_cases e : a=b+1
    · subst a
      simp
    have hk := (step_up D b (by omega : b<D)).trans <|
      mul_le_mul_of_nonneg_right (ih (by omega) (by omega)) (Real.exp_pos _).le
    rw [mul_assoc, ← Real.exp_add] at hk
    have ep : -(↑b^2-(a:ℝ)^2)/(2*D) + -(2*b+1:ℝ)/(2*D)
      = -(((↑(b+1:ℕ):ℝ))^2-(a:ℝ)^2)/(2*D) := by push_cast; ring
    rwa [ep] at hk

theorem coef_ratio_bound {D : ℕ} {b i : ℤ} (h : |i| ≤ |b|) (hi : i∈rad D) :
    coef D b / coef D i ≤ Real.exp (-((b:ℝ)^2-(i:ℝ)^2)/(2*D)) := by
  have hn (j : ℤ) : (j.natAbs:ℝ)=|(j:ℝ)| := by
    have e : (j.natAbs:ℝ)=((↑j.natAbs:ℤ):ℝ) := (Int.cast_natCast j.natAbs).symm
    rw [e,Int.natCast_natAbs, Int.cast_abs]
  have hk := coef_right_bound D i.natAbs b.natAbs (by exact_mod_cast
    (show (i.natAbs:ℤ) ≤ b.natAbs from by simpa only [Int.natCast_natAbs] using h))
  rw [coef_abs,coef_abs,hn,hn,sq_abs,sq_abs] at hk
  rw [div_le_iff₀ (coef_pos hi)]
  simpa [mul_comm] using hk


private theorem exp_trick {x : ℝ} (h : 0≤x) (e : x≤2⁻¹) :
    Real.exp (-(2*x)) ≤ 1-x := by
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  have hu : 1 ≤ (1-x)*(2*x+1) := by
    norm_num1 at e
    nlinarith
  have : 2*x+1 ≤ Real.exp (2*x) := Real.add_one_le_exp _
  nlinarith

private theorem step_dn (D i : ℕ) (h : 4*(i+1) ≤ D) :
    coef D (i:ℤ)* Real.exp (-(2*(2*i+1:ℝ)/D)) ≤ coef D (↑(i+1:ℕ)) := by
  have he : i<D := by omega
  rw [coef_step he]
  apply mul_le_mul_of_nonneg_left _ (coef_nonneg _ _)
  have hp : (0:ℝ)<D := by exact_mod_cast (by omega : 0<D)
  have e : 4*((i:ℝ)+1) ≤ D := by exact_mod_cast h
  have hh : (2*(i:ℝ)+1)/D ≤ 2⁻¹ := by rw [div_le_iff₀ hp]; norm_num; linarith
  have hz := exp_trick (by positivity) hh
  have hh' : (2*(i:ℝ)+1)/(D+i+1) ≤ (2*(i:ℝ)+1)/D :=
    div_le_div_of_nonneg_left (by positivity) hp (by linarith [show 0 ≤ (i:ℝ) by positivity])
  rw [show 2*(2*i+1:ℝ)/↑D = 2*((2*i+1:ℝ)/D) by ring]
  linarith

theorem near_coef_lower {b D : ℕ} (h : 4*b ≤ D) :
    (coef D 0)*Real.exp (-(2*(b:ℝ)^2)/D) ≤ coef D (b:ℤ) := by
  induction b with
  | zero => simp
  | succ i ih =>
    rw [Nat.cast_succ, show -(2*((i:ℝ)+1)^2)/(D:ℝ) =
      -(2*(i:ℝ)^2)/D+ -(2*(2*i+1:ℝ)/D) by ring, Real.exp_add, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right (ih (by omega)) (Real.exp_pos _).le).trans (step_dn D i h)

/-- Together with the central lower bound, this controls reciprocal table size. -/
theorem coef_lower {i : ℤ} {D : ℕ} (h : 4*|i|≤ (D:ℤ)) :
    Real.exp (-(2*(i:ℝ)^2)/D)/(2*D+1) ≤ coef D i := by
  have hm := near_coef_lower (b := i.natAbs) (D := D)
    (by exact_mod_cast (show (4:ℤ)*(i.natAbs:ℤ) ≤ (D:ℤ) from by rwa [Int.natCast_natAbs]))
  have e : (i.natAbs:ℝ)=((↑i.natAbs:ℤ):ℝ) := (Int.cast_natCast i.natAbs).symm
  rw [coef_abs,e,Int.natCast_natAbs,Int.cast_abs,sq_abs] at hm
  refine le_trans (b := 1/(2*D+1)*(Real.exp (-(2*(i:ℝ)^2)/↑D))) (le_of_eq (by ring)) ?_
  exact (mul_le_mul_of_nonneg_right (center_lower D) (Real.exp_pos _).le).trans hm

end Fourier

end IntegerMultiplication
end Computability
end OAI
