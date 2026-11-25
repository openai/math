import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Size estimates for the two-level equality-or-far label matrix

For a word of outer length `h = 2p − 1`, any term in the support polynomial
depends on at most `t = p − 1` outer coordinates. Bounding the feature count
on the other coordinates yields a saving of exactly `p²` powers of `q`.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

private theorem innerFeatureCount_le (h t q : ℕ) (hq : 0 < q) :
    1 + (h * q) ^ t ≤ (1 + h ^ t) * q ^ t := by
  rw [mul_pow, add_mul, one_mul]
  exact Nat.add_le_add_right (Nat.one_le_pow _ _ hq) _

/-- Explicit form of the `O_p(q^(-p²))` relative rank bound, with both
label counts kept integral and a constant depending only on `p`. -/
theorem outerLabelRankSavings {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    let h := 2 * p - 1
    let t := p - 1
    let r := 1 + (h * q) ^ t
    let n := q ^ h
    (1 + h ^ t) * r ^ (h - t) * n ^ t * q ^ (p ^ 2) ≤
      (1 + h ^ t) ^ (1 + (h - t)) * n ^ h := by
  dsimp only
  let h := 2 * p - 1
  let t := p - 1
  change (1 + h ^ t) * (1 + (h * q) ^ t) ^ (h - t) * (q ^ h) ^ t * q ^ (p ^ 2)
    ≤ (1 + h ^ t) ^ (1 + (h - t)) * (q ^ h) ^ h
  have h₁ : h - t = p := by dsimp [h, t]; omega
  have h₂ : h = t + p := by dsimp [h, t]; omega
  have h₃ : t * (h - t) + h * t + p ^ 2 = h * h := by
    rw [h₁, h₂]
    ring
  calc
    _ ≤ (1 + h ^ t) * ((1 + h ^ t) * q ^ t) ^ (h - t) * (q ^ h) ^ t * q ^ (p ^ 2) := by
      gcongr
      exact innerFeatureCount_le h t q hq
    _ = _ := by
      rw [mul_pow, pow_add, pow_one, ← pow_mul, ← pow_mul, ← pow_mul]
      calc
        _ = ((1 + h ^ t) * (1 + h ^ t) ^ (h - t)) *
            (q ^ (t * (h - t)) * q ^ (h * t) * q ^ (p ^ 2)) := by ring
        _ = _ := by rw [← pow_add, ← pow_add, h₃]

/-- For an alphabet of size at least the explicit `p`-dependent threshold,
the inner feature factor uses at most the number of inner words. -/
theorem innerLabelFeatureCount_le_wordCount {p q : ℕ} (hp : 0 < p)
    (hq : 1 + (2 * p - 1) ^ (p - 1) ≤ q) :
    1 + ((2 * p - 1) * q) ^ (p - 1) ≤ q ^ (2 * p - 1) := by
  let h := 2 * p - 1
  let t := p - 1
  change 1 + (h * q) ^ t ≤ q ^ h
  change 1 + h ^ t ≤ q at hq
  have hq' : 0 < q := by omega
  calc
    _ ≤ (1 + h ^ t) * q ^ t := innerFeatureCount_le h t q hq'
    _ ≤ q * q ^ t := Nat.mul_le_mul_right _ hq
    _ = q ^ (t + 1) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ q ^ h := Nat.pow_le_pow_right hq' (by dsimp [t, h]; omega)

/-- Binary exponent of the dyadic alphabet size used to batch `m` main swaps.
For `m ≥ 2` and `d > 0` this uses the bit length of `m−1`, which also
handles the case where `m` itself is a power of `2^d`. -/
def labelRadixExponent (m d : ℕ) : ℕ := (m - 1).log2 / d + 1

/-- The returned dyadic alphabet is the smallest dyadic `q` with `m ≤ q^d`.
Its `d`th power overshoots by a factor strictly less than `2^d`. -/
theorem labelRadixExponent_spec {m d : ℕ} (hm : 2 ≤ m) (hd : 0 < d) :
    let e := labelRadixExponent m d
    m ≤ (2 ^ e) ^ d ∧ (2 ^ e) ^ d < 2 ^ d * m ∧
      ∀ e' : ℕ, e' < e → (2 ^ e') ^ d < m := by
  let k := (m - 1).log2
  let e := labelRadixExponent m d
  change m ≤ (2 ^ e) ^ d ∧ (2 ^ e) ^ d < 2 ^ d * m ∧ _
  have hne : m - 1 ≠ 0 := by omega
  have hk : 2 ^ k < m := by
    have := Nat.log2_self_le hne
    dsimp [k]
    omega
  have hexp : k < e * d := by
    simpa [e, labelRadixExponent, k, Nat.mul_comm d] using Nat.lt_mul_div_succ k hd
  have upper : e * d ≤ k + d := by
    calc
      _ = k / d * d + d := by simp [e, labelRadixExponent, k, Nat.add_mul]
      _ ≤ _ := Nat.add_le_add_right (Nat.div_mul_le_self ..) _
  constructor
  · rw [← pow_mul]
    have := (Nat.log2_lt hne).mp hexp
    omega
  constructor
  · calc
      (2 ^ e) ^ d = 2 ^ (e * d) := (pow_mul ..).symm
      _ ≤ 2 ^ (k + d) := Nat.pow_le_pow_right (by decide) upper
      _ = 2 ^ d * 2 ^ k := by rw [pow_add, Nat.mul_comm]
      _ < _ := Nat.mul_lt_mul_of_pos_left hk (Nat.two_pow_pos _)
  · intro e' he'
    change e' < k / d + 1 at he'
    have hmul : e' * d ≤ k :=
      (Nat.mul_le_mul_right _ (by omega : e' ≤ k / d)).trans (Nat.div_mul_le_self ..)
    rw [← pow_mul]
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hmul) hk

end NearSquareRoot
end Computability
end OAI
