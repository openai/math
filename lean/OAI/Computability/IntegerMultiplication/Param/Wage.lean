import OAI.Computability.IntegerMultiplication.Param.Costs
import OAI.Computability.IntegerMultiplication.Grid.Tax

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Param
open Net Real
theorem direct (n):
    (Grid.tax (budget n):ℝ) ≤ 2*(lanes n:ℝ)^((9:ℝ)/10) := by
  let p := budget n
  let d:ℝ:=lanes n
  have Q : p+1≤ 2^(height n*32+1) := by
    unfold p; rw [budget_shape,pow_succ]
    have h : 0<(2:ℕ)^(height n*32) := by positivity
    omega
  have H : Grid.hail p ≤ height n*32+1 := (Nat.clog_le_iff_le_pow (by decide)).2 Q
  let k := Grid.hail (budget n)/127
  have e : 127*k ≤ height n*32+1 := by rw [mul_comm 127]; exact (Nat.div_mul_le_self (Grid.hail p) 127).trans H
  have x : (127:ℝ)*k ≤ (height n:ℝ)*32+1 := by exact_mod_cast e
  have V : lanes n=(2:ℕ)^height n := rfl
  unfold Grid.tax; rw [V]
  push_cast
  change (8:ℝ)^k ≤ _
  rw [show (8:ℝ)=(2:ℝ)^(3:ℕ) by norm_num,← pow_mul,
    ← Real.rpow_natCast,← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : 0≤(2:ℝ))]
  calc
    _ ≤ (2:ℝ)^(1+(height n)*(9/10:ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) (height n)]
    _ = _ := by
      rw [Real.rpow_add (by norm_num : 0<(2:ℝ)), Real.rpow_one]

theorem relativeTax (c:ℕ) :
    ∃ k : ℕ,∀ n a, a≤ c*(budget n+1) →
      (Grid.tax a:ℝ) ≤ k*(lanes n:ℝ)^((9:ℝ)/10) := by
  obtain ⟨k,e⟩ := Grid.snow c
  refine ⟨2*k,fun n a h=>?_⟩
  have u : (Grid.tax a:ℝ) ≤ (k:ℝ)*Grid.tax (budget n) := by exact_mod_cast e _ _ h
  exact u.trans ((mul_le_mul_of_nonneg_left (direct n) (Nat.cast_nonneg _)).trans (le_of_eq (by push_cast; ring)))

theorem taxFund (c:ℕ) :
    ∃ k : ℕ,∀ n a, a≤ c*(budget n+1) →
      (Grid.tax a:ℝ) * ((span_ n:ℝ)+1) ≤ k * fund n := by
  obtain ⟨k,e⟩:= relativeTax c
  refine ⟨k*2,fun n a h=>?_⟩
  let d:= (lanes n:ℝ)
  have w : (span_ n:ℝ)+1≤2*d^(31:ℕ) := by unfold d; exact_mod_cast spanThrifty n
  have i := e n a h
  calc
    _ ≤ k*d^((9:ℝ)/10)*(2*d^(31:ℕ)) := by gcongr
    _ = (k*2:ℕ)*d^(31+(9:ℝ)/10) := by
      have H : (d^(31:ℝ))=d^(31:ℕ) := by simpa only [Nat.cast_ofNat] using Real.rpow_natCast d 31
      rw [Real.rpow_add (show 0<d by unfold d; linarith [man n]),H]
      push_cast; ring
    _ ≤ _ := by
      gcongr
      exact under _ _ allow.2.2.2

/-- many tabulateds (e.g. imaging). -/
theorem sparseFund (c:ℕ) :
    ∃ k : ℕ,∀ n a, a≤ c*(budget n+1) →
      (Grid.tax a:ℝ)*(lanes n:ℝ) * ((lanes n:ℝ)^29+1) ≤ k * fund n := by
  obtain ⟨k,e⟩ := relativeTax c
  refine ⟨k*2,fun n a h=>?_⟩
  have i := e n a h
  let d:= (lanes n:ℝ)
  have W : d^29+1 ≤ 2*d^29 := by
    have s: (1:ℝ)≤d^29 := one_le_pow₀ (man n)
    linarith
  calc
    _ ≤ k*d^((9:ℝ)/10)*d*(2*d^29) := by gcongr
    _ ≤ (k*2:ℕ)*d^(31:ℕ) := by
      have t : d^((9:ℝ)/10) ≤ d := Real.rpow_le_self_of_one_le (man n) (by norm_num)
      push_cast
      calc
       _ ≤ k*d*d*(2*d^29) := by gcongr
       _ = _ := by ring
    _ ≤ _ := by gcongr; exact ranger n 31 (le_trans (by norm_num) allow.2.2.2)

end Param

end IntegerMultiplication
end Computability
end OAI
