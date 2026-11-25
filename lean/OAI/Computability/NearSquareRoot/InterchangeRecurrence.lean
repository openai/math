import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Time per symbol of recursive field interchange

In a call on two width-`e` fields, a recursive field has width
`(e - 1) / (m + 2*a)`. The main calls carry at most `2*m^γ` units of
relative volume altogether, and the `2*a` reserve calls carry one unit each.
Strict slack in the resulting contraction absorbs the linear local work.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open Filter

/-- Select an odd data characteristic making the cost exponent of the shared
swap computation smaller than any prescribed `γ > 1/2`. -/
theorem exists_interchange_characteristic {γ : ℝ} (hγ : 1 / 2 < γ) :
    ∃ p : ℕ, p.Prime ∧ 2 < p ∧
      1 / 2 + (3 * (p : ℝ) - 1) / (p : ℝ) ^ 2 < γ := by
  obtain ⟨s : ℕ, hs⟩ := exists_nat_gt (3 / (γ - 1 / 2))
  obtain ⟨p, hps, hp⟩ := Nat.exists_infinite_primes (max 3 s)
  have hp3 : 3 ≤ p := (le_max_left ..).trans hps
  have hs' : (s : ℝ) ≤ p := by exact_mod_cast (le_max_right 3 s).trans hps
  have hp' : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hg : 0 < γ - 1 / 2 := sub_pos.mpr hγ
  have hrs := (div_lt_iff₀ hg).mp (lt_of_lt_of_le hs hs')
  refine ⟨p, hp, by omega, ?_⟩
  have hr : (3 * (p : ℝ) - 1) / (p : ℝ) ^ 2 < γ - 1 / 2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hp')).mpr
    nlinarith [mul_lt_mul_of_pos_right hrs hp']
  linarith

/-- If the number of reserve pairs grows at most as a smaller power, the
contraction inequality holds for every sufficiently large choice of the finite
stage width. The constants in this choice may depend on the stage family. -/
theorem eventually_interchange_contraction {α γ β D : ℝ} (a : ℕ → ℕ)
    (hγα : γ < α) (hβγ : β ≤ γ) (hD : 0 ≤ D)
    (ha : ∀ᶠ m in atTop, (a m : ℝ) ≤ D * (m : ℝ) ^ β) :
    ∀ᶠ m : ℕ in atTop,
      2 * (m : ℝ) ^ γ + 2 * a m < (m : ℝ) ^ α := by
  have hlim : Tendsto (fun m : ℕ => (m : ℝ) ^ (α - γ)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hγα)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ha, eventually_ge_atTop 1, hlim.eventually_gt_atTop (2 + 2 * D)]
    with m ham hm hpow
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  have ha' : (a m : ℝ) ≤ D * (m : ℝ) ^ γ :=
    ham.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hm1 hβγ) hD)
  calc
    2 * (m : ℝ) ^ γ + 2 * a m ≤ (2 + 2 * D) * (m : ℝ) ^ γ := by linarith
    _ < (m : ℝ) ^ (α - γ) * (m : ℝ) ^ γ :=
      mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hm0 _)
    _ = (m : ℝ) ^ α := by rw [← Real.rpow_add hm0, sub_add_cancel]

/-- Width of each main or reserve field in a recursive interchange. -/
def interchangeChildWidth (m a e : ℕ) : ℕ := (e - 1) / (m + 2 * a)

/-- Solve the normalized-time recurrence, uniformly in any spectator dimensions that
were already bounded in `T`. Both the local work and the bounded-width cases may have
constants depending on the chosen finite stage. -/
theorem interchange_time_bound
    (m a : ℕ) (α γ C B : ℝ) (T : ℕ → ℝ)
    (hm : 0 < m) (hα : 0 ≤ α) (hB : 0 ≤ B)
    (hcontract : 2 * (m : ℝ) ^ γ + 2 * a < (m : ℝ) ^ α)
    (hbase : ∀ e, 0 < e → interchangeChildWidth m a e = 0 → T e ≤ B)
    (hstep : ∀ e, 0 < interchangeChildWidth m a e →
      T e ≤ C + (2 * (m : ℝ) ^ γ + 2 * a) * T (interchangeChildWidth m a e)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ e : ℕ, 0 < e → T e ≤ K * (e : ℝ) ^ α := by
  let d := 2 * (m : ℝ) ^ γ + 2 * a
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hgap : 0 < (m : ℝ) ^ α - d := sub_pos.mpr hcontract
  let K := max B (C / ((m : ℝ) ^ α - d))
  have hBK : B ≤ K := le_max_left ..
  have hK : 0 ≤ K := hB.trans hBK
  have hC : C ≤ K * ((m : ℝ) ^ α - d) :=
    (div_le_iff₀ hgap).mp (le_max_right ..)
  refine ⟨K, hK, fun e => ?_⟩
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro he
    let f := interchangeChildWidth m a e
    by_cases hf : f = 0
    · have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
      rw [← mul_one K] at hBK
      exact (hbase e he hf).trans (hBK.trans (by
        simpa using mul_le_mul_of_nonneg_left (Real.one_le_rpow he' hα) hK))
    · have hfpos : 0 < f := Nat.pos_of_ne_zero hf
      have hfsmall : f < e :=
        lt_of_le_of_lt (Nat.div_le_self ..) (by omega : e - 1 < e)
      have hfm : f * m ≤ e := calc
        f * m ≤ f * (m + 2 * a) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ e - 1 := Nat.div_mul_le_self ..
        _ ≤ e := Nat.sub_le ..
      have hfm' : (f : ℝ) * m ≤ e := by exact_mod_cast hfm
      have hpow : (f : ℝ) ^ α * (m : ℝ) ^ α ≤ (e : ℝ) ^ α := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        exact Real.rpow_le_rpow (by positivity) hfm' hα
      have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hfpos
      have hpay : C ≤ K * ((m : ℝ) ^ α - d) * (f : ℝ) ^ α :=
        hC.trans (le_mul_of_one_le_right (mul_nonneg hK hgap.le) (Real.one_le_rpow hf' hα))
      calc
        T e ≤ C + d * T f := hstep e hfpos
        _ ≤ C + d * (K * (f : ℝ) ^ α) := by gcongr; exact ih f hfsmall hfpos
        _ ≤ K * ((f : ℝ) ^ α * (m : ℝ) ^ α) := by linarith
        _ ≤ K * (e : ℝ) ^ α := mul_le_mul_of_nonneg_left hpow hK

end NearSquareRoot
end Computability
end OAI
