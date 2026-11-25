import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Positivity

/-! Binary sizes of the normalized numerator and denominator of a bounded dyadic ratio. -/

open scoped Rat

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

theorem dyadic_entry_size (m : ℤ) (k : ℕ) (hm : |m| ≤ 2 ^ k) :
    let r := (m : ℚ) / (2 : ℚ)^k
    r.num.natAbs.size ≤ k + 1 ∧ r.den.size ≤ k + 1 := by
  intro r
  have he : r = m /. (2 : ℤ)^k := by
    rw [← Rat.intCast_div_eq_divInt]; simp [r]
  have hdvd : (r.den : ℤ) ∣ (2 : ℤ)^k := he ▸ Rat.den_dvd ..
  have hd : r.den ≤ 2 ^ k := Nat.le_of_dvd (by positivity) (by exact_mod_cast hdvd)
  have ha : |r| ≤ 1 := by
    dsimp only [r]
    rw [abs_div, abs_of_pos (by positivity : 0 < (2 : ℚ)^k), div_le_one (by positivity)]
    exact_mod_cast hm
  have hpd : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  rw [← Rat.num_div_den r, abs_div, abs_of_pos hpd, div_le_one hpd] at ha
  have hz : |r.num| ≤ (r.den : ℤ) := by exact_mod_cast ha
  rw [Int.abs_eq_natAbs] at hz
  have hn : r.num.natAbs ≤ r.den := by exact_mod_cast hz
  have hb := Nat.size_le_size hd
  rw [Nat.size_pow] at hb
  exact ⟨(Nat.size_le_size hn).trans hb, hb⟩

end Lattice
end LinearProgramming
end Optimization
end OAI
