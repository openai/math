import OAI.Optimization.LinearProgramming.Games.Recovery
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Size

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Games
namespace Stochastic

def denominatorBound (n Q W : ℕ) : ℕ := n.factorial * (Q*(3+W))^n

def slopeBound (A W : ℕ) : ℕ := (W+4)*A

def chanceDiscount (A H : ℕ) : ℚ := 1/(32*(H:ℚ)*(A:ℚ)^2)

def chancePrecision (A : ℕ) : ℚ := 1/(16*(A:ℚ)^2)

theorem denominatorBound_pos (n W : ℕ) {Q : ℕ} (hQ : 0 < Q) :
    0 < denominatorBound n Q W := by unfold denominatorBound; positivity

theorem slopeBound_pos (W : ℕ) {A : ℕ} (hA : 0 < A) : 0 < slopeBound A W := by
  unfold slopeBound
  positivity

/-- The factorial and exponentiation in the discount bound give polynomial
binary length in the explicitly specified numbers, including at n = 0. -/
theorem denominatorBound_size (n Q W : ℕ) :
    (denominatorBound n Q W).size ≤ n*(n.size+Q.size+W.size+2)+1 := by
  have h₁ := (Nat.lt_size_self n).le
  have h₂ := (Nat.lt_size_self Q).le
  have h₃ : 3+W ≤ 2^(W.size+2) := by
    rw [pow_add]
    have := Nat.lt_size_self W
    have := Nat.two_pow_pos W.size
    omega
  have hb : n*(Q*(3+W)) ≤ 2^(n.size+Q.size+W.size+2) := by
    calc
      _ ≤ 2^n.size*(2^Q.size*2^(W.size+2)) := Nat.mul_le_mul h₁ (Nat.mul_le_mul h₂ h₃)
      _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hbound : denominatorBound n Q W ≤ 2^(n*(n.size+Q.size+W.size+2)) := by
    calc
      _ ≤ n^n*(Q*(3+W))^n := Nat.mul_le_mul_right _ n.factorial_le_pow
      _ = (n*(Q*(3+W)))^n := (mul_pow ..).symm
      _ ≤ (2^(n.size+Q.size+W.size+2))^n := Nat.pow_le_pow_left hb _
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  simpa only [Nat.size_pow] using Nat.size_le_size hbound

theorem chanceDiscount_bounds {A H : ℕ} (hA : 0 < A) (hH : 0 < H) :
    0 < chanceDiscount A H ∧ chanceDiscount A H ≤ 1 ∧
      chanceDiscount A H ≤ 1/(2*(H:ℚ)) ∧
      2*(H:ℚ)*chanceDiscount A H = chancePrecision A := by
  have h₁ : (1:ℚ) ≤ A := by exact_mod_cast hA
  have h₂ : (1:ℚ) ≤ H := by exact_mod_cast hH
  have h₃ : 1 ≤ (A:ℚ)^2 := one_le_pow₀ h₁
  have h₄ : (2:ℚ)*H ≤ 32*(H:ℚ)*(A:ℚ)^2 := by
    calc
      _ ≤ 32*(H:ℚ) := by linarith
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left h₃ (by positivity : (0:ℚ) ≤ 32*H)
  unfold chanceDiscount chancePrecision
  refine ⟨by positivity, (div_le_one₀ (by positivity)).mpr (by linarith),
    one_div_le_one_div_of_le (by positivity) h₄, ?_⟩
  field_simp
  ring

/-- The two independent errors, from discounting and evaluation, meet the
radius required for exact rational reconstruction in Corollary 9.4. -/
theorem recover_after_discount {A H : ℕ} (hA : 0 < A) (hH : 0 < H)
    {g z : ℚ} {v : ℝ} (hden : g.den ≤ A)
    (hdisc : |v-(g:ℝ)| ≤ 2*(H:ℝ)*chanceDiscount A H)
    (heval : |(z:ℝ)-v| ≤ chancePrecision A) :
    reconstructValue z A = some g := by
  apply reconstructValue_eq hden
  have he := (chanceDiscount_bounds hA hH).2.2.2
  have he' : 2*(H:ℝ)*(chanceDiscount A H : ℝ) = (chancePrecision A : ℝ) := by exact_mod_cast he
  rw [he'] at hdisc
  have h := (abs_sub_le (z:ℝ) v g).trans (add_le_add heval hdisc)
  have hb : (chancePrecision A : ℝ) + chancePrecision A = 1/(8*(A:ℝ)^2) := by
    simp only [chancePrecision, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_natCast]
    field_simp
    ring
  rw [hb] at h
  have hh : (↑(|z-g| : ℚ) : ℝ) ≤ (↑(1/(8*(A:ℚ)^2) : ℚ) : ℝ) := by
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
      Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast] using h
  exact Rat.cast_le.mp hh

end Stochastic
end Games
end LinearProgramming
end Optimization
end OAI
