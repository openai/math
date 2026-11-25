import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI
/-! # Cost and gap estimates for stable radix packing -/

namespace Hierarchy.Tagged.Radix
open Filter Asymptotics
open scoped Topology

theorem dyadic_pack_choice {x : ℝ} (hx : 1 ≤ x) :
    ∃ j : ℕ, x ≤ (2:ℝ)^j ∧ (2:ℝ)^j < 2*x := by
  obtain ⟨q, lo, hi⟩ := exists_nat_pow_near hx (by norm_num : 1 < (2:ℝ))
  rcases lo.eq_or_lt with eq | strict
  · exact ⟨q, eq.ge, by linarith⟩
  · refine ⟨q+1, hi.le, ?_⟩
    rw [pow_succ]
    linarith

/-- Rounding a digit width down to an integer loses at most a factor of two
once the proposed width is at least two bits. -/
theorem rounded_digit {x : ℝ} (hx : 2 ≤ x) :
    x/2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x := by
  have lo := Nat.lt_floor_add_one x
  exact ⟨by linarith, Nat.floor_le (by linarith)⟩

theorem pass_count_factor {h a digit count : ℝ} (height : 1 ≤ h)
    (ha : 1 ≤ a) (lower : h^(1/a)/2 ≤ digit) (countBound : count ≤ h/digit+1) :
    count ≤ 3*h^(1-1/a) := by
  have hp : 0 < h := by linarith
  have root : 0 < h^(1/a) := Real.rpow_pos_of_pos hp _
  have hd : 0 < digit := by linarith
  have inv : 1/a ≤ 1 := (div_le_one (by linarith : (0:ℝ)<a)).mpr ha
  have last : 1 ≤ h^(1-1/a) := Real.one_le_rpow height (by linarith)
  have product : h^(1-1/a)*h^(1/a) = h := by
    rw [← Real.rpow_add hp, sub_add_cancel, Real.rpow_one]
  have divs : h/digit ≤ 2*h^(1-1/a) := by
    apply (div_le_iff₀ hd).mpr
    have scaled := mul_le_mul_of_nonneg_left lower
      (show 0 ≤ h^(1-1/a) from Real.rpow_nonneg hp.le _)
    nlinarith
  linarith

/-- Summing the local sorts, wide pack sort and scans across all digit passes
adds the pass exponent to the larger of the two sorting exponents. -/
theorem packing_price {h x y pass base constant : ℝ}
    (height : 1 ≤ h) (hx : 0 ≤ x) (hb : 0 ≤ base) (_hc : 0 ≤ constant)
    {passes price : ℝ} (passes_nonneg : 0 ≤ passes)
    (count : passes ≤ constant * h ^ pass)
    (bill : price ≤ base * (h ^ x + h ^ y + 1)) :
    passes * price ≤ 3 * constant * base * h ^ (pass + max x y) := by
  let m := max x y
  have one : 1 ≤ h ^ m := Real.one_le_rpow height (hx.trans (le_max_left ..))
  have first : h ^ x ≤ h ^ m := Real.rpow_le_rpow_of_exponent_le height (le_max_left ..)
  have second : h ^ y ≤ h ^ m := Real.rpow_le_rpow_of_exponent_le height (le_max_right ..)
  have onePass : price ≤ base * (3 * h ^ m) :=
    bill.trans (mul_le_mul_of_nonneg_left (by linarith) hb)
  calc
    passes * price ≤ passes * (base * (3 * h ^ m)) :=
      mul_le_mul_of_nonneg_left onePass passes_nonneg
    _ ≤ (constant * h ^ pass) * (base * (3 * h ^ m)) :=
      mul_le_mul_of_nonneg_right count (by positivity)
    _ = _ := by rw [Real.rpow_add (by linarith : 0 < h)]; dsimp [m]; ring

/-- A polynomial divisor of a component gap and a substitution loss of at most
half that gap can be paid by increasing the coefficient of the squared logarithm. -/
theorem packing_gap {L C b n q gap loss : ℝ} (hL : 1 ≤ L) (hb : 0 ≤ b) (hn : 0 ≤ n)
    (hq : 0 < q) (polynomial : q ≤ (2 : ℝ) ^ (b * L))
    (component : n / (q * 2 ^ (C * L^2)) ≤ gap) (substitution : loss ≤ gap / 2) :
    n / (2 : ℝ) ^ ((C + b + 1) * L^2) ≤ gap - loss := by
  have sq : L ≤ L^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hL) (by linarith : 0 ≤ L)]
  have exponents : 1 + b*L + C*L^2 ≤ (C+b+1)*L^2 := by
    nlinarith [mul_le_mul_of_nonneg_left sq hb]
  let den := q * (2 : ℝ) ^ (C * L^2)
  have dp : 0 < den := by dsimp [den]; positivity
  have larger : 2 * den ≤ (2 : ℝ) ^ ((C+b+1)*L^2) := calc
    _ ≤ 2 * ((2 : ℝ) ^ (b*L) * 2 ^ (C*L^2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right polynomial (by positivity)) (by norm_num)
    _ = (2 : ℝ) ^ (1+b*L+C*L^2) := by
      rw [Real.rpow_add (by norm_num : (0:ℝ)<2), Real.rpow_add (by norm_num : (0:ℝ)<2),
        Real.rpow_one]; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) exponents
  have gpos : 0 ≤ gap := (div_nonneg hn dp.le).trans component
  have nbound : n ≤ gap * den := (div_le_iff₀ dp).mp component
  apply (div_le_iff₀ (by positivity)).mpr
  calc
    n ≤ gap * den := nbound
    _ ≤ (gap-loss)*(2*den) := by nlinarith [mul_nonneg (by linarith : 0 ≤ gap-2*loss) dp.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left larger (by linarith)

/-- Exponent form of the fact that the number of substituted gates is negligible
beside the gap. Here the binary logarithm is written as a quotient. -/
theorem eventual_log_budget (C b : ℝ) :
    ∀ᶠ h : ℝ in atTop, C*(Real.log (2*h)/Real.log 2)^2 +
      b*(Real.log (2*h)/Real.log 2) ≤ h/2 := by
  let A := C/(Real.log 2)^2
  let B := b/Real.log 2
  have sq : (fun x : ℝ => (Real.log x)^2) =o[atTop] fun x => x := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : 0 < (1 : ℝ))
  have lin : Real.log =o[atTop] fun x => x := Real.isLittleO_log_id_atTop
  have small := (sq.const_mul_left A).add (lin.const_mul_left B)
  have scale : Tendsto (fun h : ℝ => 2*h) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : 0 < (2:ℝ))).2 tendsto_id
  filter_upwards [scale.eventually (small.def (by norm_num : 0 < (1/4:ℝ))),
    eventually_ge_atTop (0:ℝ)] with h budget pos
  have pos' : 0 ≤ 2*h := by positivity
  have absBound : |A*(Real.log (2*h))^2+B*Real.log (2*h)| ≤ (1/4)*(2*h) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg pos'] using budget
  have upper := (le_abs_self _).trans absBound
  calc
    _ = A*(Real.log (2*h))^2+B*Real.log (2*h) := by dsimp [A,B]; rw [div_pow]; ring
    _ ≤ _ := by linarith

theorem eventual_substitution_room (C b : ℝ) :
    ∀ᶠ h : ℝ in atTop, let L := Real.log (2*h)/Real.log 2
      (2 : ℝ) ^ (b*L) ≤ 2^h / (2 * 2^(C*L^2)) := by
  filter_upwards [eventual_log_budget C b, eventually_ge_atTop (2:ℝ)] with h small large
  dsimp only
  let L := Real.log (2*h)/Real.log 2
  change (2:ℝ)^(b*L) ≤ 2^h/(2*2^(C*L^2))
  change C*L^2+b*L ≤ h/2 at small
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = (2 : ℝ) ^ (b*L+1+C*L^2) := by
      rw [Real.rpow_add (by norm_num : (0:ℝ)<2), Real.rpow_add (by norm_num : (0:ℝ)<2),
        Real.rpow_one]; ring
    _ ≤ 2^h := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- Removing the pricing slack and taking the infimum over pack widths gives
the asserted width-profile inequality, including the endpoint width one. -/
theorem packing_infimum (r : ℝ → ℝ) {a : ℝ} (ha : 1 < a)
    (priced : ∀ B : ℝ, 1 < B → ∀ e : ℝ, 0 < e →
      r 1 ≤ 1-1/a + max ((r a+e)/a) (r B+e)) :
    r 1 ≤ 1-1/a + max (r a/a) (sInf (r '' Set.Ici 1)) := by
  have apos : 0 < a := by linarith
  let t := 1-1/a
  have tp : 0 ≤ t := sub_nonneg.mpr ((div_le_one apos).mpr ha.le)
  have all (B : ℝ) (hB : 1 < B) : r 1 ≤ t + max (r a/a) (r B) := by
    apply le_of_forall_pos_le_add
    intro e he
    have ediv : e/a ≤ e := (div_le_iff₀ apos).mpr (by nlinarith [mul_nonneg he.le (sub_nonneg.mpr ha.le)])
    have above : max ((r a+e)/a) (r B+e) ≤ max (r a/a) (r B)+e := by
      apply max_le
      · rw [add_div]
        exact add_le_add (le_max_left ..) ediv
      · exact add_le_add (le_max_right ..) le_rfl
    have cost := priced B hB e he
    dsimp [t]
    linarith
  by_cases first : r 1 ≤ t + r a/a
  · exact first.trans (add_le_add le_rfl (le_max_left ..))
  · have inf : r 1 - t ≤ sInf (r '' Set.Ici 1) := by
      apply le_csInf (Set.image_nonempty.mpr ⟨1, (le_rfl : (1:ℝ) ≤ 1)⟩)
      rintro y ⟨B, hB, rfl⟩
      change 1 ≤ B at hB
      rcases hB.eq_or_lt with eq | gt
      · subst B
        linarith
      · have either : r 1-t ≤ max (r a/a) (r B) := by linarith [all B gt]
        exact (le_max_iff.mp either).resolve_left (by linarith)
    have rise : r 1 - t ≤ max (r a/a) (sInf (r '' Set.Ici 1)) := inf.trans (le_max_right ..)
    change r 1 ≤ t + _
    linarith

end Hierarchy.Tagged.Radix

end OAI
