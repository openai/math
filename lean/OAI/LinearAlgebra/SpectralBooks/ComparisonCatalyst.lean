import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Tactic.Ring

/-!
# Removing an additive catalyst from strict comparison

A one-unit gain in an ordered semiring can be amplified while reusing its
additive catalyst. Bounding the resulting multiplicative catalyst by a natural
number gives a uniform comparison of all positive powers.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {S : Type*} [CommSemiring S] [Preorder S] [IsOrderedAddMonoid S] [IsOrderedMonoid S]

omit [IsOrderedMonoid S] in
private theorem reuse_additive_catalyst {a b w : S} (h : a + w ≤ b + w) (n : ℕ) :
    (n : S) * a + w ≤ n * b + w := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ((n + 1 : ℕ) : S) * a + w = a + (n * a + w) := by push_cast; ring
      _ ≤ a + (n * b + w) := add_le_add_right ih _
      _ = n * b + (a + w) := by ring
      _ ≤ n * b + (b + w) := add_le_add_right h _
      _ = ((n + 1 : ℕ) : S) * b + w := by push_cast; ring

/-- A strict additive gain yields a single natural overhead for every power. -/
theorem powerComparison_of_additiveGain
    (hzero : ∀ z : S, 0 ≤ z) (hbound : ∀ z : S, ∃ n : ℕ, z ≤ (n : S))
    {x y : S} (hy : 1 ≤ y) (gain : ∃ s w : S, 1 + s * x + w ≤ s * y + w) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → x ^ n ≤ C • y ^ n := by
  obtain ⟨s, w, hgain⟩ := gain
  obtain ⟨j, hj⟩ := hbound w
  let J : S := (j : S) + 1
  have hJ : 1 ≤ J := by
    simpa only [J, zero_add] using add_le_add_left (hzero (j : S)) 1
  have hw : w ≤ J * y := calc
    w ≤ (j : S) := hj
    _ ≤ J := by simpa only [J, add_zero] using add_le_add_right (hzero 1) (j : S)
    _ = J * 1 := (mul_one _).symm
    _ ≤ J * y := mul_le_mul_right hy J
  obtain ⟨r, hr⟩ := hbound (J * x)
  let t : S := r * s + J
  have ht : 1 ≤ t := hJ.trans (by
    simpa only [t, zero_add] using add_le_add_left (hzero ((r : S) * s)) J)
  have hxy : t * x ≤ t * y := calc
    t * x = r * s * x + J * x := by dsimp [t]; ring
    _ ≤ r * s * x + r := add_le_add_right hr _
    _ = r * (1 + s * x) + 0 := by ring
    _ ≤ r * (1 + s * x) + w := add_le_add_right (hzero w) _
    _ ≤ r * (s * y) + w := reuse_additive_catalyst hgain r
    _ ≤ r * (s * y) + J * y := add_le_add_right hw _
    _ = t * y := by dsimp [t]; ring
  have hpow (n : ℕ) : t * x ^ n ≤ t * y ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        t * x ^ (n + 1) = (t * x ^ n) * x := by rw [pow_succ, mul_assoc]
        _ ≤ (t * y ^ n) * x := mul_le_mul_left ih x
        _ = (t * x) * y ^ n := by ring
        _ ≤ (t * y) * y ^ n := mul_le_mul_left hxy _
        _ = t * y ^ (n + 1) := by ring
  obtain ⟨c, hc⟩ := hbound t
  refine ⟨c + 1, Nat.succ_pos _, fun n _ => ?_⟩
  calc
    x ^ n = 1 * x ^ n := (one_mul _).symm
    _ ≤ t * x ^ n := mul_le_mul_left ht _
    _ ≤ t * y ^ n := hpow n
    _ ≤ (c : S) * y ^ n := mul_le_mul_left hc _
    _ ≤ (c + 1) • y ^ n := by
      simpa only [succ_nsmul, nsmul_eq_mul, add_zero] using
        add_le_add_right (hzero (y ^ n)) ((c : S) * y ^ n)

end SpectralBooks
end LinearAlgebra
end OAI
