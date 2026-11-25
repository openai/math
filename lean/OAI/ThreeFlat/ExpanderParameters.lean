import OAI.ThreeFlat.ExpanderParameterRatio
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic

namespace OAI
/-! # Dyadic port sizes for bounded-degree amplification -/

namespace ThreeFlat.Expander

/-- Choose the sparse kernel's dimension, its power-of-two degree, and an even
dyadic time for which the cloud matching has integral multiplicities. Both
iteration depth and base dimension may be chosen above prescribed thresholds. -/
theorem exists_amplification_parameters {α C : ℝ}
    (hα : 0 < α) (h3 : α < 3) (hC : 0 ≤ C) (j₀ n₀ : ℕ) :
    ∃ j ≥ j₀, ∃ n ≥ n₀, ∃ a b : ℕ,
      let D : ℕ := 2^n
      let Q := D^(3^j)
      let t : ℕ := 2*2^a
      let h : ℕ := 2^b
      2*28^j*D ≤ h ∧ h ≤ 4*28^j*D ∧ t*(4*h)^t ∣ Q ∧
        1728 * max 1 (C * α^j) / (t : ℝ) ≤ 1/2 := by
  obtain ⟨j, hj, hratio⟩ := exists_amplification_index hα h3 hC (max j₀ 2)
  have hj₂ : 2 ≤ j := (le_max_right _ _).trans hj
  let L : ℕ := 3^j
  have hL : 4 ≤ L := (by decide : 4 ≤ (3:ℕ)^2).trans (Nat.pow_le_pow_right (by decide) hj₂)
  have hlog : 2 ≤ L.log2 := (Nat.le_log2 (by omega)).mpr (by simpa using hL)
  let a := L.log2 - 2
  let t : ℕ := 2*2^a
  have ht : 0 < t := by dsimp [t]; positivity
  have htPow : t = 2^(a+1) := by simp [t, pow_succ, Nat.mul_comm]
  have htwice : 2*t = 2^L.log2 := by
    have eqn : a+2 = L.log2 := Nat.sub_add_cancel hlog
    rw [← eqn, pow_add]
    dsimp [t]
    ring
  have htL : t < L := by
    have hbound := Nat.log2_self_le (n := L) (by omega)
    omega
  have hLt : L < 4*t := by
    calc
      _ < 2^(L.log2+1) := Nat.lt_log2_self
      _ = _ := by rw [pow_succ, ← htwice]; ring
  let f : ℕ := 28^j
  let m := f.log2 + 2
  have hf : f ≠ 0 := by dsimp [f]; positivity
  have hmlo : 2*f ≤ 2^m := by
    calc
      _ ≤ 2 * 2^(f.log2+1) := Nat.mul_le_mul_left 2 Nat.lt_log2_self.le
      _ = _ := by simp [m, pow_succ, Nat.mul_comm]
  have hmhi : 2^m ≤ 4*f := by
    calc
      _ = 4*2^f.log2 := by simp [m, pow_add, Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left 4 (Nat.log2_self_le hf)
  let n := max n₀ (a+1 + (m+2)*t)
  let b := n+m
  refine ⟨j,(le_max_left _ _).trans hj,n,le_max_left _ _,a,b,?_⟩
  change 2*f*2^n ≤ 2^b ∧ 2^b ≤ 4*f*2^n ∧ t*(4*2^b)^t ∣ (2^n)^(3^j) ∧ _
  have hb : (2:ℕ)^b = 2^m*2^n := by
    change 2^(n+m) = _
    rw [pow_add, Nat.mul_comm]
  refine ⟨by rw [hb]; exact Nat.mul_le_mul_right _ hmlo,
    by rw [hb]; exact Nat.mul_le_mul_right _ hmhi, ?_, ?_⟩
  · have expo : a+1 + (2+b)*t ≤ n*L := by
      calc
        _ = (a+1+(m+2)*t) + n*t := by dsimp [b]; ring
        _ ≤ n + n*t := Nat.add_le_add_right (le_max_right _ _) _
        _ = n*(t+1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left n htL
    have hfour : 4*2^b = (2:ℕ)^(2+b) := by rw [pow_add (2:ℕ) 2 b]; norm_num
    have hin : t*(4*2^b)^t = (2:ℕ)^(a+1+(2+b)*t) := by
      calc
        _ = 2^(a+1) * (2^(2+b))^t := by rw [← htPow, hfour]
        _ = _ := by rw [pow_add (2:ℕ) (a+1) ((2+b)*t), pow_mul (2:ℕ) (2+b) t]
    rw [hin, ← pow_mul]
    exact Nat.pow_dvd_pow 2 expo
  · change 1728 * max 1 (C * α^j) / (t : ℝ) ≤ 1/2
    have hLt' : (3 : ℝ)^j < 4 * (t : ℝ) := by
      change 3^j < 4*t at hLt
      exact_mod_cast hLt
    apply (div_le_iff₀ (by exact_mod_cast ht : (0:ℝ)<t)).mpr
    linarith

end ThreeFlat.Expander

end OAI
