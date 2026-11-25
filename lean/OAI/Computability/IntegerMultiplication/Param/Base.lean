import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- Eventually in the task input length = n.
All top arithmetic setup will use natural numbers as below. -/
namespace Param
open Filter Set Real Topology
abbrev Large (q : ℕ → Prop) := ∀ᶠ n in atTop, q n

theorem beats (c k : ℕ) : Large fun n=> c*n^k ≤ 2^n := by
  have v := tendsto_pow_const_div_const_pow_of_one_lt k (r:=2) (by norm_num)
  have s (c : ℕ) := (v.const_mul (c:ℝ)).eventually (gt_mem_nhds (by norm_num : (c:ℝ)*0<1)) -- mul target c*0
  filter_upwards [s c] with n hn
--  dsimp only [mem_Iio] at hn
  have e : (c:ℝ)*(n:ℝ)^k < 2^n := by simpa only [one_mul] using ((div_lt_iff₀ (by positivity : (0:ℝ)<2^n)).mp (by rw [mul_div_assoc]; exact hn : (c:ℝ)*(n:ℝ)^k/(2:ℝ)^n<1))
  exact_mod_cast le_of_lt e

theorem logBound (n : ℕ) : 2^Nat.clog 2 n ≤ 2*(n+1) := by
  cases n with
  | zero => simp
  | succ n =>
    by_cases e : 1 < n+1
    · have h : 0 < Nat.clog 2 (n+1) := Nat.clog_pos (by decide) e
      have t : 2^(Nat.clog 2 (n+1)).pred < n+1 :=
        Nat.pow_pred_clog_lt_self (by decide) e
      rw [show Nat.clog 2 (n+1)=(Nat.clog 2 (n+1)).pred+1 from (Nat.succ_pred_eq_of_pos h).symm,pow_succ]
      omega
    · have : n=0 := by omega
      subst n; simp

theorem clog_flees : Tendsto (Nat.clog 2) atTop atTop := by
  refine tendsto_atTop.2 fun n=>?_
  filter_upwards [eventually_gt_atTop ((2:ℕ)^n)] with x h
  have v := Nat.le_pow_clog (b:=2) (by decide) x
  by_contra! e
  have Q := Nat.pow_le_pow_right (by decide : 0 < 2) e.le
  omega

theorem limitAbove {f g : ℕ → ℕ} (h : ∀ n,f n≤ g n) (t : Tendsto f atTop atTop) :
    Tendsto g atTop atTop := by
  refine tendsto_atTop.2 fun b=>?_
  filter_upwards [t.eventually (eventually_ge_atTop b)] with i hh
  exact hh.trans (h i)

def beta n := max 1 (Nat.clog 2 n)
def height n := Nat.clog 2 (4*beta n) /32 +1
def lanes n := (2:ℕ)^height n
def budget n := lanes n^32
-- eventual lower bounds

theorem beta_grows : Tendsto beta atTop atTop :=
  limitAbove (f:=Nat.clog 2) (fun _=>Nat.le_max_right ..) clog_flees

theorem twolog : Tendsto (fun n=> Nat.clog 2 (4*beta n)) atTop atTop :=
  clog_flees.comp (limitAbove (g:=fun n=>4*beta n) (fun n=> by omega) beta_grows)

theorem height_grows : Tendsto height atTop atTop := by
  refine tendsto_atTop.2 fun m=>?_
  filter_upwards [twolog.eventually (eventually_ge_atTop (m*32))] with n hn
  unfold height
  calc
    _ ≤ Nat.clog 2 (4*beta n)/32 := (Nat.le_div_iff_mul_le (by decide)).2 hn
    _ ≤ _ := by omega

theorem dim_grows : Tendsto lanes atTop atTop :=
  limitAbove (g:=lanes) (f:=height) (fun n=> (Nat.lt_pow_self (a:=2) (n:=height n) (by decide)).le) height_grows

theorem lanes_pos (n) : 0 < lanes n := Nat.pow_pos (by decide)
theorem budget_p (n) : 0 < budget n := Nat.pow_pos (lanes_pos _)
theorem budget_shape (n) : budget n=2^(height n*32) := by rw [budget,lanes,pow_mul]

theorem four_beta (n): 4*beta n ≤ budget n := by
  rw [budget_shape]
  apply (Nat.le_pow_clog (b:=2) (by decide) _).trans
  apply Nat.pow_le_pow_right (by decide)
  unfold height
  omega

theorem beyond (n) : budget n ≤ 2^36 * beta n := by
  rw [budget_shape]
  have h : height n*32 ≤ 32+Nat.clog 2 (4*beta n) := by unfold height; omega
  have w : 0< beta n := by unfold beta; omega
  apply (Nat.pow_le_pow_right (n:=2) (by decide) h).trans
  rw [pow_add]
  have l := logBound (4*beta n)
  norm_num1 at *
  omega

theorem ringlet (c k:ℕ) :
    Large fun n=> c*budget n^k ≤ n := by
  filter_upwards [beta_grows.eventually (beats (2*c*(2^36)^k) k),eventually_gt_atTop (1:ℕ)] with n hn n_
  have l : 2^beta n ≤ 2*n := by
    unfold beta
    have h := Nat.clog_pos (b:=2) (by decide) n_
    rw [max_eq_right h,
      show Nat.clog 2 n=(Nat.clog 2 n).pred+1 from (Nat.succ_pred_eq_of_pos h).symm,
      pow_succ]
    have t := Nat.pow_pred_clog_lt_self (b:=2) (by decide) n_
    omega
  have s : 2*c*budget n^k ≤ 2*n :=
    calc
      _ ≤ 2*c*(2^36*beta n)^k := by gcongr; exact beyond n
      _ = (2*c*(2^36)^k)*beta n^k := by rw [mul_pow]; ring
      _ ≤ _ := hn.trans l
  nlinarith

end Param

end IntegerMultiplication
end Computability
end OAI
