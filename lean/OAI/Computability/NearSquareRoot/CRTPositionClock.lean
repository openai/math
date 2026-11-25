import OAI.Computability.NearSquareRoot.CRTPositionProgramTableRate
import OAI.Computability.NearSquareRoot.CRTControlledSizes

/-! # Time and high-prefix capacity of a compiled position sweep -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open Filter

noncomputable def positionRate (ρ : ℝ) (k : ℕ) : ℝ :=
  ((1 + Nat.clog 2 (k+1) : ℕ) : ℝ) * ((k+1:ℕ):ℝ)^ρ

noncomputable def positionFactor (ρ : ℝ) (k : ℕ) : ℕ := ⌈2 * positionRate ρ k⌉₊

theorem tableRate_eq (ρ : ℝ) (k w : ℕ) :
    tableRate ρ k w = ((2^k:ℕ):ℝ) * w * positionRate ρ k := by
  unfold tableRate rowRate positionRate; ring

theorem one_le_positionRate {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) : 1 ≤ positionRate ρ k := by
  unfold positionRate
  exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.le_add_right 1 _)
    (Real.one_le_rpow (by exact_mod_cast Nat.succ_pos k) hρ)

theorem positionRate_mono {ρ : ℝ} (hρ : 0 ≤ ρ) : Monotone (positionRate ρ) := by
  intro k j h
  have log := Nat.clog_mono_right 2 (Nat.succ_le_succ h)
  unfold positionRate
  gcongr

theorem positionFactor_pays {ρ : ℝ} (hρ : 0 ≤ ρ) {m k : ℕ} (h : m ≤ k) :
    2 * positionRate ρ m ≤ positionFactor ρ k :=
  (mul_le_mul_of_nonneg_left (positionRate_mono hρ h) (by norm_num)).trans (Nat.le_ceil _)

theorem positionFactor_time {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) :
    (positionFactor ρ k : ℝ)+1 ≤ 4 * positionRate ρ k := by
  have one := one_le_positionRate hρ k
  have up := Nat.ceil_lt_add_one (a:=2 * positionRate ρ k) (by linarith)
  unfold positionFactor; linarith

/-- The high prefix to serialize the full sweep has logarithmic, fixed-coefficient width. -/
theorem positionFactor_high {ρ : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    positionFactor ρ k ≤ 2^(payloadBits (⌈ρ⌉₊+2) k) := by
  have clog : Nat.clog 2 (k+1) ≤ k := Nat.clog_le_of_le_pow (show k < 2^k from Nat.lt_two_pow_self)
  have one : 1 ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  have two : 2 ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hk
  have power := Real.rpow_le_rpow_of_exponent_le one (Nat.le_ceil ρ)
  rw [Real.rpow_natCast] at power
  have c : ((1+Nat.clog 2 (k+1):ℕ):ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1+Nat.clog 2 (k+1) ≤ k+1)
  apply (show positionFactor ρ k ≤ (k+1)^(⌈ρ⌉₊+2) from ?_).trans
    (by simpa using payload_capacity (⌈ρ⌉₊+2) k 1 (by decide))
  apply Nat.ceil_le.mpr
  unfold positionRate
  push_cast
  calc
    _ ≤ ((k:ℝ)+1) * (((k:ℝ)+1) * ((k:ℝ)+1)^⌈ρ⌉₊) := by
      push_cast at c power two
      gcongr
    _ = _ := by rw [pow_add]; ring

/-- Time for both logarithmic gathers and the entire guarded interior, measured
against the original address volume. -/
theorem reserve_clock {ρ : ℝ} (hρ : 0 ≤ ρ) (a b k : ℕ) :
    ((payloadBits a k+payloadBits b k+1:ℕ):ℝ) + ((positionFactor ρ k:ℝ)+1) ≤
      (a+b+5:ℕ) * positionRate ρ k := by
  have one : 1 ≤ ((k+1:ℕ):ℝ)^ρ := Real.one_le_rpow (by exact_mod_cast Nat.succ_pos k) hρ
  have log : ((1+Nat.clog 2 (k+1):ℕ):ℝ) ≤ positionRate ρ k :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) one
  have gather : ((payloadBits a k+payloadBits b k+1:ℕ):ℝ) ≤ (a+b+1:ℕ)*positionRate ρ k := by
    apply le_trans _ (mul_le_mul_of_nonneg_left log (Nat.cast_nonneg _))
    exact_mod_cast (show payloadBits a k+payloadBits b k+1 ≤ (a+b+1)*(1+Nat.clog 2 (k+1)) by
      unfold payloadBits; rw [Nat.add_mul,Nat.add_mul,Nat.mul_add,Nat.mul_add]; omega)
  have factor := positionFactor_time hρ k
  push_cast at gather ⊢
  linarith only [gather,factor]

/-- Any fixed multiple of the full position factor and all reserve-gather scans
fit under any strictly larger exponent, retaining the native record volume. -/
theorem eventually_position_slack {ρ α : ℝ} (h : ρ < α) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop, C * positionRate ρ k ≤ ((k+1:ℕ):ℝ)^α := by
  let c := 1 + (Real.log 2)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have tends : Tendsto (fun k : ℕ => ((k+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have main := tends.eventually (eventually_logSlack (C*(1+c)) (by positivity) 1 h)
  filter_upwards [main] with k bound
  let x : ℝ := ((k+1 : ℕ) : ℝ)
  have positive : 1 ≤ x := by dsimp [x]; exact_mod_cast Nat.succ_pos k
  have log := clog_le_logScale (n := k+1) (by omega)
  change (((max 1 (Nat.clog 2 (k+1)) : ℕ) : ℝ)) ≤ c*(1+Real.log x) at log
  have co : (Nat.clog 2 (k+1):ℝ) ≤ c*(1+Real.log x) :=
    (show ((Nat.clog 2 (k+1):ℕ):ℝ) ≤ ((max 1 (Nat.clog 2 (k+1)):ℕ):ℝ) by exact_mod_cast Nat.le_max_right ..).trans log
  have all : ((1+Nat.clog 2 (k+1):ℕ):ℝ) ≤ (1+c)*(1+Real.log x) := by
    have hl := Real.log_nonneg positive; push_cast; linarith
  change C * (((1 + Nat.clog 2 (k+1) : ℕ):ℝ) * x^ρ) ≤ x^α
  change C*(1+c)*(1+Real.log x)^1*x^ρ ≤ x^α at bound
  calc
    _ ≤ C * (((1+c)*(1+Real.log x)) * x^ρ) := by gcongr
    _ = C*(1+c)*(1+Real.log x)^1*x^ρ := by ring
    _ ≤ _ := bound

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
