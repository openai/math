import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

/-!
# The exponent in the uniform multiplication bound

Here `T n` is a single worst-case step count. Constants and length thresholds
may depend on the accuracy requested for the exponent.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open Filter
open scoped Topology

noncomputable def logScale (n : ℕ) : ℝ := 1 + Real.log n

theorem tendsto_logScale : Tendsto logScale atTop atTop :=
  tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- An eventual upper bound for each fixed positive excess exponent. -/
def AllEpsilonBounds (T : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n in atTop, (T n : ℝ) ≤ C * n * logScale n ^ ((1 : ℝ) / 2 + ε)

/-- The upper bound with one excess exponent tending to zero. -/
def VanishingExponentBound (T : ℕ → ℕ) : Prop :=
  ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
    ∀ᶠ n in atTop, (T n : ℝ) ≤ n * logScale n ^ ((1 : ℝ) / 2 + δ n)

/-- Half the available excess exponent absorbs the multiplicative constant. -/
theorem AllEpsilonBounds.eventually_le {T : ℕ → ℕ} (h : AllEpsilonBounds T)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (T n : ℝ) ≤ n * logScale n ^ ((1 : ℝ) / 2 + ε) := by
  have hp : 0 < ε / 2 := half_pos hε
  obtain ⟨C, _, hC⟩ := h (ε / 2) hp
  have hpow : Tendsto (fun n => logScale n ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop hp).comp tendsto_logScale
  filter_upwards [hC, hpow.eventually_ge_atTop C,
    tendsto_logScale.eventually_gt_atTop 0] with n hn hCn hpos
  calc
    (T n : ℝ) ≤ C * n * logScale n ^ ((1 : ℝ) / 2 + ε / 2) := hn
    _ ≤ logScale n ^ (ε / 2) * n * logScale n ^ ((1 : ℝ) / 2 + ε / 2) := by
      gcongr
    _ = n * (logScale n ^ (ε / 2) * logScale n ^ ((1 : ℝ) / 2 + ε / 2)) := by ring
    _ = n * logScale n ^ ((1 : ℝ) / 2 + ε) := by
      rw [← Real.rpow_add hpos]
      congr 2
      ring

theorem allEpsilonBounds_iff_vanishingExponentBound (T : ℕ → ℕ) :
    AllEpsilonBounds T ↔ VanishingExponentBound T := by
  constructor
  · intro h
    -- The positive part also works when the actual time is smaller than the
    -- leading square-root bound or even zero.
    let ratio (n : ℕ) : ℝ := max 1 ((T n : ℝ) / n)
    let δ (n : ℕ) : ℝ := max 0 (Real.logb (logScale n) (ratio n) - 1 / 2)
    have hratio (n : ℕ) : 0 < ratio n := zero_lt_one.trans_le (le_max_left ..)
    refine ⟨δ, tendsto_order.mpr ⟨?_, ?_⟩, ?_⟩
    · intro a ha
      exact .of_forall fun n => ha.trans_le (le_max_left ..)
    · intro ε hε
      have hp := half_pos hε
      filter_upwards [h.eventually_le hp, tendsto_logScale.eventually_gt_atTop 1,
        eventually_gt_atTop (0 : ℕ)] with n hT hb hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hlog : Real.logb (logScale n) (ratio n) ≤ 1 / 2 + ε / 2 := by
        apply (Real.logb_le_iff_le_rpow hb (hratio n)).mpr
        refine max_le (Real.one_le_rpow hb.le (by linarith)) ?_
        exact (div_le_iff₀ hn').mpr (by simpa [mul_comm] using hT)
      change max 0 (Real.logb (logScale n) (ratio n) - 1 / 2) < ε
      exact max_lt hε (by linarith)
    · filter_upwards [tendsto_logScale.eventually_gt_atTop 1, eventually_gt_atTop (0 : ℕ)]
        with n hb hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hlog : Real.logb (logScale n) (ratio n) ≤ 1 / 2 + δ n := by
        have := le_max_right 0 (Real.logb (logScale n) (ratio n) - 1 / 2)
        dsimp only [δ]
        linarith
      have hquot := (le_max_right 1 ((T n : ℝ) / n)).trans
        ((Real.logb_le_iff_le_rpow hb (hratio n)).mp hlog)
      simpa [mul_comm] using (div_le_iff₀ hn').mp hquot
  · rintro ⟨δ, hδ, hT⟩ ε hε
    refine ⟨1, zero_lt_one, ?_⟩
    filter_upwards [hT, hδ.eventually_le_const hε, tendsto_logScale.eventually_ge_atTop 1]
      with n hn hδn hb
    rw [one_mul]
    exact hn.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hb (by linarith)) (Nat.cast_nonneg _))

/-- Candidate index `j` gives excess exponent `1/(j+2)` for the same step count. -/
theorem allEpsilonBounds_of_indexed {T : ℕ → ℕ}
    (h : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (T n : ℝ) ≤ C * n * logScale n ^ ((1 : ℝ) / 2 + 1 / (j + 2 : ℝ))) :
    AllEpsilonBounds T := by
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  obtain ⟨C, hpos, hC⟩ := h j
  refine ⟨C, hpos, ?_⟩
  have hsmall : 1 / (j + 2 : ℝ) ≤ 1 / (j + 1 : ℝ) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  filter_upwards [hC, tendsto_logScale.eventually_ge_atTop 1] with n hn hb
  exact hn.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hb (by linarith)) (by positivity))

/-- Compare the binary ceiling logarithm used in the P192 machine accounting
with the positive logarithmic scale in the asymptotic statement. -/
theorem clog_le_logScale {n : ℕ} (hn : 0 < n) :
    (max 1 (Nat.clog 2 n) : ℕ) ≤ (1 + (Real.log 2)⁻¹) * logScale n := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog := Real.log_nonneg hn'
  have h2 : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_nonneg (by norm_num))
  have hceil := (Nat.ceil_lt_add_one (Real.logb_nonneg (b := (2 : ℝ)) (by norm_num) hn')).le
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · unfold logScale
    nlinarith [mul_nonneg h2 hlog]
  · rw [← Real.natCeil_logb_natCast]
    norm_num only [Nat.cast_ofNat] at *
    refine hceil.trans ?_
    unfold logScale Real.logb
    rw [div_eq_mul_inv]
    nlinarith

/-- Upper bounds proved with a binary ceiling logarithm imply the real-log
bounds, with the change of base included in each exponent's constant. -/
theorem allEpsilonBounds_of_clog {T : ℕ → ℕ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (T n : ℝ) ≤ C * n * (max 1 (Nat.clog 2 n) : ℕ) ^ ((1 : ℝ) / 2 + ε)) :
    AllEpsilonBounds T := by
  intro ε hε
  obtain ⟨C, hC, hT⟩ := h ε hε
  let K := 1 + (Real.log 2)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  let a := (1 : ℝ) / 2 + ε
  have ha : 0 ≤ a := by dsimp [a]; linarith
  refine ⟨C * K ^ a, by positivity, ?_⟩
  filter_upwards [hT, eventually_gt_atTop (0 : ℕ), tendsto_logScale.eventually_ge_atTop 0]
      with n hn hnpos hb
  calc
    (T n : ℝ) ≤ C * n * (max 1 (Nat.clog 2 n) : ℕ) ^ a := hn
    _ ≤ C * n * (K * logScale n) ^ a :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (clog_le_logScale hnpos) ha) (by positivity)
    _ = C * K ^ a * n * logScale n ^ a := by rw [Real.mul_rpow hK.le hb]; ring

/-- At a fixed nonnegative exponent, one larger constant covers every positive
width. The original natural clock is kept for the finitely many short inputs. -/
theorem fixedExponentBound_forall_pos {T : ℕ → ℕ} {γ C : ℝ} (hγ : 0 ≤ γ) (hC : 0 < C)
    (hT : ∀ᶠ n in atTop, (T n : ℝ) ≤ C * n * logScale n ^ γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n → (T n : ℝ) ≤ K * n * logScale n ^ γ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hT
  let M : ℕ := ∑ i ∈ Finset.range N, T i
  refine ⟨max C M, hC.trans_le (le_max_left ..), ?_⟩
  intro n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : 1 ≤ logScale n := by
    unfold logScale
    linarith [Real.log_nonneg hn']
  have hpow : 1 ≤ logScale n ^ γ :=
    Real.one_le_rpow hb hγ
  by_cases hl : N ≤ n
  · exact (hN n hl).trans (by gcongr; exact le_max_left ..)
  · have hm : T n ≤ M := Finset.single_le_sum (f := T)
        (fun i _ => Nat.zero_le (T i)) (Finset.mem_range.mpr (by omega : n < N))
    have hbound : (T n : ℝ) ≤ max C (M : ℝ) :=
      (show (T n : ℝ) ≤ M by exact_mod_cast hm).trans (le_max_right ..)
    calc
      (T n : ℝ) ≤ max C (M : ℝ) := hbound
      _ = max C (M : ℝ) * 1 * 1 := by ring
      _ ≤ max C (M : ℝ) * n * logScale n ^ γ := by gcongr

/-- For natural step counts, the constant can cover every positive input length. -/
theorem allEpsilonBounds_iff_forall_pos (T : ℕ → ℕ) :
    AllEpsilonBounds T ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 0 < n → (T n : ℝ) ≤ C * n * logScale n ^ ((1 : ℝ) / 2 + ε) := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hT⟩ := h ε hε
    exact fixedExponentBound_forall_pos (by linarith) hC hT
  · intro h ε hε
    obtain ⟨C, hC, hT⟩ := h ε hε
    exact ⟨C, hC, (eventually_gt_atTop 0).mono hT⟩

end NearSquareRoot
end Computability
end OAI
