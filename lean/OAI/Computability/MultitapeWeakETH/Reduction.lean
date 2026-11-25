import OAI.Computability.MultitapeWeakETH.Tables
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Sqrt

/-! # From coarse traces and partial tables to the tape bound -/

namespace OAI.Computability.MultitapeWeakETH

open Filter

private theorem block_estimates (n : ℕ) (hn : 4 ≤ n) :
    let b := n.sqrt + 1
    let m := n ⌈/⌉ b
    n.sqrt ≤ m ∧ n ≤ b * m ∧ n ≤ m ^ 4 := by
  dsimp only
  let m := n ⌈/⌉ (n.sqrt+1)
  have cover : n ≤ (n.sqrt+1)*m := (ceilDiv_le_iff_le_mul (Nat.succ_pos _)).mp le_rfl
  have hs : n.sqrt ≤ m := by
    by_contra! h
    have := Nat.mul_le_mul_left (n.sqrt+1) (Nat.succ_le_of_lt h)
    nlinarith [Nat.sqrt_le n]
  have two : 2 ≤ m := (Nat.le_sqrt.mpr hn).trans hs
  refine ⟨hs, cover, cover.trans ?_⟩
  calc
    _ ≤ (m+1)*m := Nat.mul_le_mul_right _ (by omega)
    _ ≤ m^2*m^2 := Nat.mul_le_mul (by nlinarith [Nat.mul_le_mul_left m two])
      (by nlinarith [Nat.mul_le_mul_left m two])
    _ = _ := by ring

private theorem eventually_trace_loss (A : ℕ) (hA : 0 < A) :
    ∀ᶠ n : ℕ in atTop, ∀ T : ℕ, (T : ℝ) ≤ scale n →
      A * (1 + (T : ℝ) / (n.sqrt + 1 : ℕ)) ≤ (n : ℝ)/1000 := by
  have pos : (0 : ℝ) < A := by exact_mod_cast hA
  let K : ℝ := 2000 * A
  have hk : 0 < K := by dsimp [K]; positivity
  have slack : 0 < Real.log 2 / K^2 := by positivity
  have little := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Real.isLittleO_log_id_atTop.bound slack)
  filter_upwards [little, eventually_ge_atTop (2000*A+1)] with n small hn
  intro T hT
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  change ‖Real.log (n : ℝ)‖ ≤ _ * ‖(n : ℝ)‖ at small
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hn1), Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _)] at small
  let b : ℝ := (n.sqrt+1 : ℕ)
  have hb : 0 < b := by dsimp [b]; positivity
  have sq : (n : ℝ) ≤ b^2 := by dsimp [b]; exact_mod_cast (Nat.lt_succ_sqrt' n).le
  have scaled : Real.logb 2 n ≤ (b/K)^2 := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num)), div_pow]
    calc
      _ ≤ _ := small
      _ ≤ (Real.log 2 / K^2) * b^2 := mul_le_mul_of_nonneg_left sq slack.le
      _ = _ := by ring
  have root := Real.sqrt_le_sqrt scaled
  rw [Real.sqrt_sq (div_nonneg hb.le hk.le)] at root
  have dt : (T : ℝ)/b ≤ n/K := by
    apply (div_le_iff₀ hb).mpr
    exact hT.trans ((mul_le_mul_of_nonneg_left root (Nat.cast_nonneg n)).trans_eq (by ring))
  have half : (A : ℝ) ≤ (n : ℝ)/2000 := by
    have low : 2000*A ≤ n := by omega
    have realLow : (2000:ℝ)*A ≤ n := by exact_mod_cast low
    linarith
  change A * (1 + (T : ℝ)/b) ≤ _
  calc
    _ ≤ A * (1 + (n : ℝ)/K) := by gcongr
    _ = A + (n : ℝ)/2000 := by dsimp [K]; field_simp
    _ ≤ _ := by linarith

theorem retained_lower_bound (trace : CoarseTraceBound) (table : PartialTableBound)
    (M : Machine) : LowerBound (retained M) := by
  obtain ⟨D,A,hA,N,extract⟩ := trace M
  obtain ⟨c,hc,m₀,hard⟩ := table D
  have apos : (0 : ℝ) < A := by exact_mod_cast hA
  have grow := Real.tendsto_sqrt_atTop.comp ((Real.tendsto_logb_atTop
    (by norm_num : (1:ℝ) < 2)).comp tendsto_natCast_atTop_atTop)
  let constant := min 1 (c / (4*A))
  refine ⟨constant, lt_min zero_lt_one (by positivity), eventually_atTop.mp ?_⟩
  filter_upwards [eventually_ge_atTop (max 4 (max N (m₀*m₀))),
    eventually_trace_loss A hA, grow.eventually_ge_atTop (12*A/c)] with n hn loss large
  intro T good
  have hn4 : 4 ≤ n := by omega
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have nonneg : 0 ≤ scale n := mul_nonneg hnpos.le (Real.sqrt_nonneg _)
  by_cases fast : (T : ℝ) ≤ scale n
  · let b := n.sqrt+1
    let m := n ⌈/⌉ b
    obtain ⟨hs,cover,four⟩ := block_estimates n hn4
    obtain ⟨G,bounded,size,tables,goodrows⟩ := extract n (by omega) T good
    have retainedRows : (2 : ℝ)^(-(11/1000 : ℝ)*n) ≤ density (G.Good tables) := by
      refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) goodrows
      linarith [loss T fast]
    have min_m : m₀ ≤ m := (Nat.le_sqrt.mpr (by omega)).trans hs
    have lb := hard n b (Nat.succ_pos _) min_m G bounded tables retainedRows
    have logs := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hnpos
      (show (n : ℝ) ≤ (m:ℝ)^4 by exact_mod_cast four)
    rw [Real.logb_pow] at logs
    have mpos : 1 ≤ m := (Nat.le_sqrt.mpr (by omega)).trans hs
    have root := Real.sqrt_le_sqrt logs
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ (4:ℕ))] at root
    norm_num at root
    rw [show Real.sqrt 4 = 2 by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]] at root
    have sizes : (n:ℝ) ≤ (b:ℝ)*m := by exact_mod_cast cover
    have demands : c * scale n ≤ 2*((G.vertices:ℝ)*b) := by
      unfold scale at lb ⊢
      calc
        _ ≤ c * (((b:ℝ)*m) * (2 * Real.sqrt (Real.logb 2 m))) := by gcongr
        _ = 2 * ((c * (m * Real.sqrt (Real.logb 2 m))) * b) := by ring
        _ ≤ _ := by gcongr
    have bsmall : (b:ℝ) ≤ 2*n := by
      exact_mod_cast (show b ≤ 2*n by dsimp [b]; have := Nat.sqrt_le_self n; omega)
    have overhead : 12*A*n ≤ c * scale n := by
      change 12*A/c ≤ Real.sqrt (Real.logb 2 n) at large
      have aux := (div_le_iff₀ hc).mp large
      unfold scale
      nlinarith only [mul_le_mul_of_nonneg_right aux hnpos.le]
    have main : c * scale n ≤ 4*A*T := by
      nlinarith only [demands,size,overhead,mul_le_mul_of_nonneg_left bsmall apos.le]
    calc
      constant * scale n ≤ (c/(4*A))*scale n := mul_le_mul_of_nonneg_right (min_le_right ..) nonneg
      _ = (c * scale n)/(4*A) := by ring
      _ ≤ T := (div_le_iff₀ (by positivity)).mpr (by linarith)
  · exact (mul_le_of_le_one_left nonneg (min_le_left ..)).trans (le_of_not_ge fast)

theorem main_of_tables (trace : CoarseTraceBound)
    (table : PartialTableBound) : MainStatement := by
  intro M
  obtain ⟨c,hc,N,lower⟩ := retained_lower_bound trace table M
  constructor
  · refine ⟨c,hc,N,fun n hn T ⟨law,success⟩ => ?_⟩
    obtain ⟨seed,bound⟩ := fix_private_coins M n T law
    exact lower n hn T (.inl ⟨seed,success.trans bound⟩)
  · exact fun sound => ⟨c,hc,N,fun n hn T mass => lower n hn T (.inr ⟨sound,mass⟩)⟩

end OAI.Computability.MultitapeWeakETH
