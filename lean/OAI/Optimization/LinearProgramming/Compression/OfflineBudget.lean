import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-! Explicit common bounds for the short rational point and its affine evaluations in
Section 3. In particular, the exponent of the final power of two depends only on the
matrix dimension. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- Coefficient bound after clearing denominators in one clipped-form row. -/
def offlineRowCap (B E : ℕ) : ℕ :=
  let C := 2 * E
  1 + (4 * C) * C ^ 4 + C ^ 4 + (B + 17 + 4 * C) * (E * C ^ 4) + E * C ^ 4

/-- Numerator and denominator bound for a Cramer point. -/
def offlinePointCap (s K : ℕ) : ℕ := s.factorial * (K ^ (s + 2)) ^ s

/-- Bound for an affine evaluation of a point of bounded height. -/
def offlineValueCap (s C Y : ℕ) : ℕ := (s + 1) * ((C + 1) * (Y + 1)) ^ (s + 2)

theorem offlinePointCap_mono {s t K : ℕ} (hst : s ≤ t) (hK : 0 < K) :
    offlinePointCap s K ≤ offlinePointCap t K := by
  unfold offlinePointCap
  apply Nat.mul_le_mul (Nat.factorial_le hst)
  calc
    _ ≤ (K ^ (t + 2)) ^ s :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_right hK (Nat.add_le_add_right hst 2)) s
    _ ≤ _ := Nat.pow_le_pow_right (Nat.pow_pos hK) hst

theorem offlineValueCap_mono {s t C D Y Z : ℕ} (hst : s ≤ t) (hCD : C ≤ D) (hYZ : Y ≤ Z) :
    offlineValueCap s C Y ≤ offlineValueCap t D Z := by
  unfold offlineValueCap
  apply Nat.mul_le_mul (Nat.add_le_add_right hst 1)
  calc
    _ ≤ ((D + 1) * (Z + 1)) ^ (s + 2) := Nat.pow_le_pow_left
      (Nat.mul_le_mul (Nat.add_le_add_right hCD 1) (Nat.add_le_add_right hYZ 1)) _
    _ ≤ _ := Nat.pow_le_pow_right (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
      (Nat.add_le_add_right hst 2)

private theorem double_pow (n : ℕ) : 2 * (2 : ℕ) ^ n = 2 ^ (n + 1) := by
  rw [pow_succ, Nat.mul_comm]

private theorem add_one_le_next_pow {a n : ℕ} (h : a ≤ 2 ^ n) : a + 1 ≤ 2 ^ (n + 1) := by
  rw [← double_pow]
  have := Nat.two_pow_pos n
  omega

private theorem row_le_envelope (B E Z : ℕ) (hZ : 0 < Z) (he : E ≤ Z)
    (hc : 2 * E ≤ Z) (hb : B + 17 ≤ Z) : offlineRowCap B E ≤ 16 * Z ^ 6 := by
  have hc4 : (2 * E) ^ 4 ≤ Z ^ 4 := Nat.pow_le_pow_left hc 4
  have hec := Nat.mul_le_mul he hc4
  have h4c := Nat.mul_le_mul_left 4 hc
  calc
    _ ≤ 1 + (4 * Z) * Z ^ 4 + Z ^ 4 + (Z + 4 * Z) * (Z * Z ^ 4) + Z * Z ^ 4 :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add_left (Nat.mul_le_mul h4c hc4) 1) hc4)
        (Nat.mul_le_mul (Nat.add_le_add hb h4c) hec)) hec
    _ = 1 + 4 * Z ^ 5 + Z ^ 4 + 5 * Z ^ 6 + Z ^ 5 := by ring
    _ ≤ 16 * Z ^ 6 := by
      have hp : 0 < Z ^ 6 := Nat.pow_pos hZ
      have h4 : Z ^ 4 ≤ Z ^ 6 := Nat.pow_le_pow_right hZ (by decide)
      have h5 : Z ^ 5 ≤ Z ^ 6 := Nat.pow_le_pow_right hZ (by decide)
      omega

private theorem row_le_power (B n k : ℕ) (hn : n + 1 ≤ k) (hb : B + 17 ≤ k) :
    offlineRowCap B (2 ^ n) ≤ 2 ^ (4 + k * 6) := by
  have he : (2 : ℕ) ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
  have hc : 2 * (2 : ℕ) ^ n ≤ 2 ^ k :=
    (double_pow n).le.trans (Nat.pow_le_pow_right (by decide) hn)
  have hcap := row_le_envelope B (2 ^ n) (2 ^ k) (Nat.two_pow_pos _) he hc
    (hb.trans k.lt_two_pow_self.le)
  calc
    _ ≤ (2 : ℕ) ^ 4 * ((2 : ℕ) ^ k) ^ 6 := hcap
    _ = _ := by rw [← pow_mul, ← pow_add]

theorem offlineRowCap_le_two_pow (B : ℕ) :
    offlineRowCap B (2 ^ (B + 7)) ≤ 2 ^ (4 + (B + 17) * 6) :=
  row_le_power B (B + 7) (B + 17) (by omega) (le_refl _)

theorem offlinePointCap_le_two_pow (s : ℕ) {K k : ℕ} (hK : K ≤ 2 ^ k) :
    offlinePointCap s K ≤ 2 ^ (s * s + k * (s + 2) * s) := by
  have hf : s.factorial ≤ (2 ^ s) ^ s :=
    (Nat.factorial_le_pow s).trans (Nat.pow_le_pow_left s.lt_two_pow_self.le s)
  unfold offlinePointCap
  calc
    _ ≤ (2 ^ s) ^ s * ((2 ^ k) ^ (s + 2)) ^ s :=
      Nat.mul_le_mul hf (Nat.pow_le_pow_left (Nat.pow_le_pow_left hK _) _)
    _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, Nat.mul_assoc k]

/-- An explicit polynomial for the binary logarithm of the final uniform bound. -/
def offlineValueBits (N : ℕ) : ℕ :=
  let B := 100 * (N + 1) ^ 3
  let s := (N + 1) ^ 6
  let k := 4 + (B + 17) * 6
  let y := s * s + k * (s + 2) * s
  s + 1 + (B + 9 + (y + 1)) * (s + 2)

theorem offlineValueCap_le_two_pow (N : ℕ) :
    let B := 100 * (N + 1) ^ 3
    let E := 2 ^ (B + 7)
    let s := (N + 1) ^ 6
    let C := 2 * E
    let Y := offlinePointCap s (offlineRowCap B E)
    offlineValueCap s C Y ≤ 2 ^ offlineValueBits N := by
  let B := 100 * (N + 1) ^ 3
  let E := 2 ^ (B + 7)
  let s := (N + 1) ^ 6
  let C := 2 * E
  let k := 4 + (B + 17) * 6
  let Y := offlinePointCap s (offlineRowCap B E)
  let y := s * s + k * (s + 2) * s
  change (s + 1) * ((C + 1) * (Y + 1)) ^ (s + 2) ≤ 2 ^ (s + 1 + (B + 9 + (y + 1)) * (s + 2))
  have hC : C + 1 ≤ 2 ^ (B + 9) := add_one_le_next_pow (double_pow (B + 7)).le
  have hY : Y + 1 ≤ 2 ^ (y + 1) :=
    add_one_le_next_pow (offlinePointCap_le_two_pow s (offlineRowCap_le_two_pow B))
  calc
    _ ≤ 2 ^ (s + 1) * ((2 ^ (B + 9)) * (2 ^ (y + 1))) ^ (s + 2) :=
      Nat.mul_le_mul (s + 1).lt_two_pow_self.le (Nat.pow_le_pow_left (Nat.mul_le_mul hC hY) _)
    _ = _ := by rw [← pow_add, ← pow_mul, ← pow_add]

/-- A single monomial also bounds the exponent in all dimensions. -/
theorem offlineValueBits_le (N : ℕ) : offlineValueBits N ≤ 6689 * (N + 1) ^ 21 := by
  let u := N + 1
  have hu : 0 < u := Nat.succ_pos _
  have hpow (d : ℕ) (hd : d ≤ 21) : u ^ d ≤ u ^ 21 := Nat.pow_le_pow_right hu hd
  have hp : 0 < u ^ 21 := Nat.pow_pos hu
  calc
    offlineValueBits N = 600 * u ^ 21 + 107 * u ^ 18 + 2400 * u ^ 15 + 426 * u ^ 12 +
        2500 * u ^ 9 + 435 * u ^ 6 + 200 * u ^ 3 + 21 := by
      change u ^ 6 + 1 + (100 * u ^ 3 + 9 +
        (u ^ 6 * u ^ 6 + (4 + (100 * u ^ 3 + 17) * 6) * (u ^ 6 + 2) * u ^ 6 + 1)) *
        (u ^ 6 + 2) = _
      ring
    _ ≤ 6689 * u ^ 21 := by
      have h18 := hpow 18 (by decide)
      have h15 := hpow 15 (by decide)
      have h12 := hpow 12 (by decide)
      have h9 := hpow 9 (by decide)
      have h6 := hpow 6 (by decide)
      have h3 := hpow 3 (by decide)
      omega

end Compression
end LinearProgramming
end Optimization
end OAI
