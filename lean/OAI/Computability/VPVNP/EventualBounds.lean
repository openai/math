import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Order.Monotone.Basic

/-!
# Transfer of eventual circuit-size bounds under polynomial projections

Section 15.1 of *VP and VNP differ over every field* uses two properties of a
complete family: its order-`j` polynomial projects from its order-`j+1`
polynomial for `j ≥ 2`, and the hard family projects from orders at most
`A * n ^ b`. Both projections preserve upper bounds on the number of binary
gates. The result below transfers the eventual lower bounds to every order.
-/

namespace OAI
namespace Computability
namespace VPVNP

/-- The all-sufficiently-large-length lower bound for each positive exponent. -/
def EventuallySuperpolynomial (size : ℕ → ℕ) : Prop :=
  ∀ C : ℕ, 1 ≤ C → ∃ N : ℕ, ∀ n ≥ N, n ^ C < size n

/-- Section 15.1. For every order `m` above a fixed threshold, the floor root
of `m / A` supplies a length `n` whose projected order is at most `m` and whose
lower bound already exceeds `m ^ C`. The projection indices may have gaps. -/
theorem eventualBound_of_polynomialProjection
    {hard complete q : ℕ → ℕ} {A b n₀ : ℕ} (hA : 0 < A) (hb : 0 < b)
    (hhard : EventuallySuperpolynomial hard)
    (hproj : ∀ n ≥ n₀, 2 ≤ q n ∧ q n ≤ A * n ^ b ∧ hard n ≤ complete (q n))
    (hstep : ∀ j ≥ 2, complete j ≤ complete (j + 1)) (C : ℕ) :
    ∃ M : ℕ, ∀ m ≥ M, m ^ C < complete m := by
  obtain ⟨N, hN⟩ := hhard (b * C + 1) (Nat.le_add_left 1 _)
  let K := A * 2 ^ b
  let threshold := max (max N n₀) (max 1 (K ^ C))
  refine ⟨A * threshold ^ b, ?_⟩
  intro m hm
  let n := Nat.nthRoot b (m / A)
  have hn : threshold ≤ n := (Nat.le_nthRoot_iff hb.ne').mpr <|
    (Nat.le_div_iff_mul_le hA).mpr (by simpa [Nat.mul_comm] using hm)
  have hnN : N ≤ n := le_trans ((le_max_left ..).trans (le_max_left ..)) hn
  have hn₀ : n₀ ≤ n := le_trans ((le_max_right ..).trans (le_max_left ..)) hn
  have hn1 : 1 ≤ n := le_trans ((le_max_left ..).trans (le_max_right ..)) hn
  have hK : K ^ C ≤ n := le_trans ((le_max_right ..).trans (le_max_right ..)) hn
  obtain ⟨hq₂, hq, hred⟩ := hproj n hn₀
  have hqm : q n ≤ m := hq.trans <| by
    rw [Nat.mul_comm]
    exact (Nat.le_div_iff_mul_le hA).mp (Nat.pow_nthRoot_le (.inl hb.ne'))
  have hmupper : m ≤ K * n ^ b := calc
    m ≤ (n + 1) ^ b * A := ((Nat.div_lt_iff_lt_mul hA).mp
      (Nat.lt_pow_nthRoot_add_one hb.ne' (m / A))).le
    _ ≤ (2 * n) ^ b * A := Nat.mul_le_mul_right A (Nat.pow_le_pow_left (by omega) b)
    _ = K * n ^ b := by simp [K, mul_pow, Nat.mul_comm, Nat.mul_left_comm]
  calc
    m ^ C ≤ (K * n ^ b) ^ C := Nat.pow_le_pow_left hmupper C
    _ = n ^ (b * C) * K ^ C := by rw [mul_pow, pow_mul, Nat.mul_comm]
    _ ≤ n ^ (b * C + 1) := by rw [pow_succ]; exact Nat.mul_le_mul_left _ hK
    _ < hard n := hN n hnN
    _ ≤ complete (q n) := hred
    _ ≤ complete m := monotoneOn_nat_Ici_of_le_succ hstep hq₂ (hq₂.trans hqm) hqm

/-- An eventual lower bound for each exponent excludes every polynomial size
bound, including bounds with a multiplicative constant and a length cutoff. -/
theorem EventuallySuperpolynomial.not_polynomially_bounded {size : ℕ → ℕ}
    (hsize : EventuallySuperpolynomial size) :
    ¬ ∃ A d N : ℕ, ∀ n ≥ N, size n ≤ A * n ^ d := by
  rintro ⟨A, d, N, hupper⟩
  obtain ⟨M, hlower⟩ := hsize (d + 1) (Nat.le_add_left 1 d)
  let n := max A (max M N)
  have hA : A ≤ n := le_max_left ..
  have hM : M ≤ n := (le_max_left ..).trans (le_max_right ..)
  have hN : N ≤ n := (le_max_right ..).trans (le_max_right ..)
  apply (hlower n hM).not_ge
  calc
    size n ≤ A * n ^ d := hupper n hN
    _ ≤ n * n ^ d := Nat.mul_le_mul_right _ hA
    _ = n ^ (d + 1) := by rw [pow_succ, Nat.mul_comm]

end VPVNP
end Computability
end OAI
