import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI
/-! # Nonempty error sets in the lens estimate

All prices are in the scale in which the binary diagonal on the output sites
has price `c`. A term pays the rail budget and saves `D` for each erroneous
cell. The empty set of errors cancels. -/

namespace Hierarchy.GridLens
open scoped BigOperators
noncomputable section
variable {ι : Type*} [DecidableEq ι]

/-- The normalized spectral value of the error expansion, allowing up to
`2^ell` wirings for each nonempty error set. -/
def errorMass (cells : Finset ι) (ell : ℕ) (base D c : ℝ) : ℝ :=
  (2:ℝ)^ell * ∑ t ∈ cells.powerset.erase ∅, (2:ℝ)^((base-(t.card:ℝ)*D)/c)

theorem errorMass_eq (cells : Finset ι) (ell : ℕ) (base D c : ℝ) :
    errorMass cells ell base D c = (2:ℝ)^ell * (2:ℝ)^(base/c) *
      ((1+(2:ℝ)^(-D/c))^cells.card-1) := by
  let q := (2:ℝ)^(-D/c)
  have split (t : Finset ι) :
      (2:ℝ)^((base-(t.card:ℝ)*D)/c) = (2:ℝ)^(base/c)*q^t.card := by
    have e : (base-(t.card:ℝ)*D)/c = base/c + (-D/c)*(t.card:ℝ) := by ring
    rw [e, Real.rpow_add (by norm_num : (0:ℝ)<2), Real.rpow_mul_natCast (by norm_num)]
  have expand : (1+q)^cells.card = ∑ t ∈ cells.powerset, q^t.card := by
    simpa using (Finset.prod_one_add (f := fun _ : ι => q) cells)
  have hempty : (∅ : Finset ι) ∈ cells.powerset := by simp
  unfold errorMass
  simp_rw [split]
  rw [← Finset.mul_sum, Finset.sum_erase_eq_sub hempty, ← expand]
  simp [q, mul_assoc]

private theorem binomial_pos {q : ℝ} {L : ℕ} (hq : 0 < q) (hL : 0 < L) :
    0 < (1+q)^L-1 :=
  sub_pos.mpr (one_lt_pow₀ (by linarith) hL.ne')

/-- The sharp logarithmic count in the paper's lens estimate. -/
theorem log_errorMass (cells : Finset ι) (ell : ℕ) {base D c : ℝ}
    (nonempty : cells.Nonempty) (hc : 0 < c) :
    c*Real.logb 2 (errorMass cells ell base D c) =
      base + c*ell + c*Real.logb 2 ((1+(2:ℝ)^(-D/c))^cells.card-1) := by
  have hp := binomial_pos (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (-D/c))
    (Finset.card_pos.mpr nonempty)
  rw [errorMass_eq, Real.logb_mul (by positivity) hp.ne',
    Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)]
  field_simp [hc.ne']; ring

private theorem binomial_tail_le (L : ℕ) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (1+q)^L-1 ≤ (2:ℝ)^L*q := by
  induction L with
  | zero => simpa using h0
  | succ L ih =>
    have h := pow_le_pow_left₀ (show 0 ≤ 1+q by linarith) (show 1+q ≤ 2 by linarith) L
    have hh := mul_le_mul_of_nonneg_right h h0
    rw [pow_succ, pow_succ]
    linarith only [ih, hh]

/-- Coarse nonempty-error count with the saving of one full `D`. -/
theorem log_errorMass_le (cells : Finset ι) (ell : ℕ) {base D c : ℝ}
    (nonempty : cells.Nonempty) (hc : 0 < c) (hD : 0 ≤ D) :
    c*Real.logb 2 (errorMass cells ell base D c) ≤ base-D+c*((ell:ℝ)+cells.card) := by
  let q := (2:ℝ)^(-D/c)
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hD) hc.le)
  have logle := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (binomial_pos hq (Finset.card_pos.mpr nonempty)) (binomial_tail_le cells.card hq.le hq1)
  rw [Real.logb_mul (by positivity) hq.ne', Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)] at logle
  dsimp only [q] at logle
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at logle
  rw [log_errorMass cells ell nonempty hc]
  have scale : c*(-D/c) = -D := by field_simp [hc.ne']
  nlinarith only [mul_le_mul_of_nonneg_left logle hc.le, scale]

/-- Convert the spectral-value estimate for a nonzero error tensor into the
ordinary-sum estimate in price units. -/
theorem price_le_log_errorMass (cells : Finset ι) (ell : ℕ) {price base D c : ℝ}
    (hc : 0 < c) (value : (2:ℝ)^(price/c) ≤ errorMass cells ell base D c) :
    price ≤ c*Real.logb 2 (errorMass cells ell base D c) := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (price/c)) value
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at h
  calc
    price = c*(price/c) := by field_simp [hc.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left h hc.le

/-- The strict price comparison also allows a positive selector length. -/
theorem price_lt_through (cells : Finset ι) (ell k : ℕ) (nonempty : cells.Nonempty)
    {price E D R c excess : ℝ} (hc : 0 < c) (hD : 0 ≤ D) (star : c ≤ 2*k*R)
    (slack : excess+2*k*R*((ell:ℝ)+cells.card) < D)
    (value : (2:ℝ)^(price/c) ≤ errorMass cells ell (2*R*E+excess) D c) :
    price < 2*R*E := by
  have h := (price_le_log_errorMass cells ell hc value).trans
    (log_errorMass_le cells ell nonempty hc hD)
  have charge := mul_le_mul_of_nonneg_right star (show (0:ℝ) ≤ (ell:ℝ)+cells.card by positivity)
  linarith

/-- After the geometric excess and the error count each use at most one
quarter of the initial gap, rescaling the focus distance back to one retains
the gap `D/(2R)`. -/
theorem reuse_gap (cells : Finset ι) (nonempty : cells.Nonempty) {price E D R c excess : ℝ}
    (k : ℕ) (hR : 0 < R) (hc : 0 < c) (hD : 0 < D) (star : c ≤ 2*k*R)
    (rail : excess ≤ D/4) (count : 2*k*R*cells.card ≤ D/4)
    (value : price ≤ c*Real.logb 2 (errorMass cells 0 (2*R*E+excess) D c)) :
    price/R ≤ 2*E - D/(2*R) ∧ price/R < 2*E := by
  have bound := value.trans (log_errorMass_le cells 0 nonempty hc hD.le)
  simp only [Nat.cast_zero,zero_add] at bound
  have star' := mul_le_mul_of_nonneg_right star (Nat.cast_nonneg cells.card : (0:ℝ) ≤ cells.card)
  have raw : price ≤ 2*R*E - D/2 := by linarith
  have result : price/R ≤ 2*E - D/(2*R) := by
    apply (div_le_iff₀ hR).mpr
    calc
      price ≤ 2*R*E - D/2 := raw
      _ = _ := by field_simp [hR.ne']
  exact ⟨result, result.trans_lt (sub_lt_self _ (div_pos hD (by positivity)))⟩

/-- A single explicit focus radius works for every wiring with rail excess
at most `numerator/R` and counting cost at most `slope*R`. -/
theorem reuse_radius {g D numerator slope : ℝ} (hg : 0 < g) (hD : 0 < D)
    (cells : 32*g*slope ≤ D) (rails : 16*numerator*slope ≤ D^2) :
    let R := max (8*g) (4*numerator/D)
    0 < R ∧ 8*g ≤ R ∧ numerator/R ≤ D/4 ∧ slope*R ≤ D/4 := by
  let R := max (8*g) (4*numerator/D)
  have far : 8*g ≤ R := le_max_left _ _
  have hR : 0 < R := (mul_pos (by norm_num) hg).trans_le far
  have need : 4*numerator/D ≤ R := le_max_right _ _
  refine ⟨hR, far, (div_le_iff₀ hR).mpr ?_, ?_⟩
  · nlinarith only [(div_le_iff₀ hD).mp need]
  · rcases le_total (8*g) (4*numerator/D) with h | h
    · rw [max_eq_right h, ← mul_div_assoc]
      apply (div_le_iff₀ hD).mpr
      nlinarith only [rails]
    · rw [max_eq_left h]
      linarith only [cells]


end
end Hierarchy.GridLens

end OAI
