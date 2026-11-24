import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Linarith

/-!
# Choosing the port count for the averaged lazy walk

In Section 5.3 of *VP and VNP differ over every field*, the mean of the first
`t` positive powers of a lazy walk on a `b`-regular graph has common
denominator `t * (2 * b) ^ t`. The port set has size `Q = D ^ (4 * t)`.
Here `t`, `D` and `b` are powers of two. A sufficiently large choice of `D`
makes the port count divisible by this denominator for *every* rounded
degree satisfying the support bound `2 * b ≤ 16 * C * D`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

/-- Sufficient size conditions for the divisibility in the first paragraph
of the port construction. -/
theorem walk_denominator_dvd_port_count {k d e C : ℕ}
    (ht : 2 ^ k ≤ 2 ^ d) (hC : 16 * C ≤ 2 ^ d)
    (hdegree : 2 * 2 ^ e ≤ 16 * C * 2 ^ d) :
    2 ^ k * (2 * 2 ^ e) ^ (2 ^ k) ∣ (2 ^ d) ^ (4 * 2 ^ k) := by
  have hkd : k ≤ d := (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp ht
  have hpower : 2 ^ (1 + e) ≤ (2 : ℕ) ^ (d + d) := by
    rw [pow_add, pow_one, pow_add]
    exact hdegree.trans (Nat.mul_le_mul_right _ hC)
  have he : 1 + e ≤ d + d := (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hpower
  have htpos := Nat.two_pow_pos k
  have hkt : k ≤ d * 2 ^ k := hkd.trans (Nat.le_mul_of_pos_right _ htpos)
  have hexp : k + (1 + e) * 2 ^ k ≤ d * (4 * 2 ^ k) := by
    nlinarith only [hkt, Nat.mul_le_mul_right (2 ^ k) he]
  have hb : 2 * 2 ^ e = (2 : ℕ) ^ (1 + e) := by rw [pow_add, pow_one]
  rw [hb, ← pow_mul, ← pow_add, ← pow_mul]
  exact pow_dvd_pow _ hexp

/-- The sparse recursion may request arbitrarily large starting order `D`.
Choose it before the rounded degree `b` is known. -/
theorem exists_walk_port_order (k C minimum : ℕ) :
    ∃ d : ℕ, minimum ≤ 2 ^ d ∧ 2 ≤ 2 ^ d ∧
      ∀ e : ℕ, 2 * 2 ^ e ≤ 16 * C * 2 ^ d →
        2 ^ k * (2 * 2 ^ e) ^ (2 ^ k) ∣ (2 ^ d) ^ (4 * 2 ^ k) := by
  let d := max k (max (16 * C) (max minimum 1))
  have hkd : k ≤ d := le_max_left _ _
  have hCd : 16 * C ≤ d := (le_max_left _ _).trans (le_max_right _ _)
  have hm : minimum ≤ d := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h1 : 1 ≤ d := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hd : d < 2 ^ d := Nat.lt_two_pow_self
  refine ⟨d, hm.trans hd.le, by omega, fun _ he ↦ ?_⟩
  exact walk_denominator_dvd_port_count (Nat.pow_le_pow_right (by decide) hkd) (hCd.trans hd.le) he

/-- When the sparse Poincaré bound grows like `α ^ j` with `α < m = 2^r`,
choose `j` so that the even smoothing length `t = m^j / 4` dominates the
rounded port bound `β = max 1 (2*C' * α^j)` by the factor `1776` used in
the cloud iteration. -/
theorem exists_walk_smoothing_scale (r : ℕ) (hr : 0 < r) {α : ℝ} (hα : 1 ≤ α)
    (hsmall : α < 2 ^ r) (C' : ℝ) :
    ∃ j k : ℕ, 0 < k ∧ ((2 : ℕ) ^ r) ^ j = 4 * 2 ^ k ∧
      1776 * max 1 (2 * C' * α ^ j) ≤ (2 : ℝ) ^ k := by
  let B := max 1 (2 * C')
  have hB : 1 ≤ B := le_max_left _ _
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hm : 0 < (2 : ℝ) ^ r := by positivity
  have hratio : α / 2 ^ r < 1 := (div_lt_one hm).mpr hsmall
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < 1 / (7104 * B)) hratio
  let j := i + 3
  let k := r * j - 2
  have hrj : 3 ≤ r * j := by
    have := Nat.le_mul_of_pos_left j hr
    dsimp [j] at *
    omega
  have hk : k + 2 = r * j := Nat.sub_add_cancel (by omega)
  have hcard : ((2 : ℕ) ^ r) ^ j = 4 * 2 ^ k := by
    rw [← pow_mul, ← hk, pow_add]; omega
  have hsmallj : (α / 2 ^ r) ^ j ≤ 1 / (7104 * B) := by
    refine le_trans ?_ hi.le
    exact pow_le_pow_of_le_one (div_nonneg (by linarith) hm.le) hratio.le (by dsimp [j]; omega)
  rw [div_pow] at hsmallj
  have hscale := (div_le_div_iff₀ (pow_pos hm _) (by positivity)).mp hsmallj
  have hreal : ((2 : ℝ) ^ r) ^ j = 4 * 2 ^ k := by exact_mod_cast hcard
  have hpower : 1 ≤ α ^ j := one_le_pow₀ hα
  have hbeta : max 1 (2 * C' * α ^ j) ≤ B * α ^ j := max_le
    (one_le_mul_of_one_le_of_one_le hB hpower)
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith only [hpower]))
  refine ⟨j, k, by dsimp [k]; omega, hcard, ?_⟩
  linarith only [hreal, hscale, hbeta]

end SpectralGeometry

end VPVNP
end Computability
end OAI
