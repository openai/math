import OAI.Computability.VPVNP.PolynomialBounds
import OAI.Computability.VPVNP.LiveEvaluatorTail
import OAI.Computability.VPVNP.RAMParameters
import OAI.Computability.VPVNP.RAMClock

/-! # Choosing the length and field widths of the diagonal chain

Section 9.1 fixes the chain height using the evaluator's running time before
choosing the processor-address multiplier. The exponent width itself depends
on the height. The evaluator's polynomial factor in that width is absorbed
in the tail clock without increasing the exponent of its exponential factor.
The cut-width exponent is also chosen before the processor multiplier, since
its quartic word width is eventually at most the input length for each fixed
multiplier.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace DiagonalClock

open Filter BurstRAM LiveEvaluatorEncoding

private theorem power_bound {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ᶠ n : ℕ in atTop, f n ≤ n^c := by
  obtain ⟨A,d,N,h⟩ := hf
  refine ⟨d+1, by omega, ?_⟩
  filter_upwards [eventually_ge_atTop A, eventually_ge_atTop N] with n ha hn
  rw [pow_succ, Nat.mul_comm]
  exact (h n hn).trans (Nat.mul_le_mul_right _ ha)

/-- On exponent inputs of width `Z=2 n^a`, the singly exponential evaluator
fits in the `2^(n^a-1)` tail groups. The polynomial degree in `Z` may be
arbitrary, and the choice of `a` depends only on the exponent envelope. -/
theorem tail_clock {P : ℕ → ℕ} (hp : PolynomiallyBounded P) : ∃ a : ℕ, 2 ≤ a ∧ ∀ k : ℕ,
    ∀ᶠ n : ℕ in atTop, 2^(P n) * (2*n^a+1)^k ≤ 2^(n^a-1) := by
  obtain ⟨c,hc,hP⟩ := power_bound hp
  let a := c+2
  refine ⟨a, by dsimp [a]; omega, fun k => ?_⟩
  filter_upwards [hP, eventually_ge_atTop (max 3 ((a+2)*k+2))] with n hn hn'
  have hn3 := (le_max_left ..).trans hn'
  have hm := (le_max_right ..).trans hn'
  have hpos : 0 < n^a := Nat.pow_pos (by omega)
  have hsmall : 2*n^a+1 ≤ n^(a+2) := by
    rw [pow_add n a 2]
    have hnn : 3 ≤ n^2 := by rw [pow_two]; nlinarith
    exact (by omega : 2*n^a+1 ≤ n^a*3).trans (Nat.mul_le_mul_left _ hnn)
  have hpw : n^((a+2)*k) ≤ 2^(n*((a+2)*k)) := by
    rw [pow_mul 2 n ((a+2)*k)]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  have he : n^c + n*((a+2)*k) < n^a := by
    have hcn : n ≤ n^c := by simpa using Nat.pow_le_pow_right (by omega : 0 < n) hc
    have hterm : n*((a+2)*k) ≤ n^c*((a+2)*k) := Nat.mul_le_mul_right _ hcn
    have hn2 : 1 + (a+2)*k < n^2 := by rw [pow_two]; nlinarith
    change n^c + n*((a+2)*k) < n^(c+2)
    rw [pow_add n c 2]
    calc
      _ ≤ n^c * (1 + (a+2)*k) := by rw [Nat.mul_add, Nat.mul_one]; omega
      _ < n^c * n^2 := Nat.mul_lt_mul_of_pos_left hn2 (Nat.pow_pos (by omega))
  calc
    _ ≤ 2^(n^c) * (n^(a+2))^k := Nat.mul_le_mul
      (Nat.pow_le_pow_right (by decide) hn) (Nat.pow_le_pow_left hsmall _)
    _ ≤ 2^(n^c) * 2^(n*((a+2)*k)) := Nat.mul_le_mul_left _ (by rw [← pow_mul]; exact hpw)
    _ = 2^(n^c + n*((a+2)*k)) := (pow_add ..).symm
    _ ≤ 2^(n^a-1) := Nat.pow_le_pow_right (by decide) (by omega)

/-- The order of choices of `a,d₁,d₂,B` for the evaluator. A polynomial tape
radius at every fixed polynomial exponent width suffices, independently of
its exponentially larger clock. -/
theorem parameters {P advice labels : ℕ → ℕ} (radius : ℕ → ℕ → ℕ)
    (hp : PolynomiallyBounded P) (ha : PolynomiallyBounded advice)
    (ht : PolynomiallyBounded labels)
    (hr : ∀ a, PolynomiallyBounded fun n => radius n (2*n^a)) (E : UniversalMachine.Program) :
    ∃ a d₁ d₂ : ℕ, 2 ≤ a ∧ ∀ k B : ℕ, 1 ≤ B → ∀ᶠ n : ℕ in atTop,
      let Z := 2*n^a
      let w := (addressWidth B n + 10)^4
      2^(P n) * (Z+1)^k ≤ 2^(n^a-1) ∧ advice n ≤ n^d₁ ∧
        1 + labels n * Z ≤ n^d₂ ∧ LiveEvaluatorTail.Layout E.extra (radius n Z) w (n^d₂) := by
  obtain ⟨a,ha2,hclock⟩ := tail_clock hp
  obtain ⟨d₁,_,had⟩ := power_bound ha
  let space := hr a
  have hf : PolynomiallyBounded (fun n => fieldWords (radius n (2*n^a))) :=
    (((PolynomiallyBounded.const 1).add (((PolynomiallyBounded.const 2).mul space).add (.const 1))).add
      (((PolynomiallyBounded.const 2).mul space).add (.const 1)))
  have hz := (PolynomiallyBounded.const 2).mul (PolynomiallyBounded.id.pow a)
  obtain ⟨d₂,_,hΔ⟩ := power_bound (((PolynomiallyBounded.const 1).add (ht.mul hz)).add
    ((PolynomiallyBounded.const 1).add (hf.mul PolynomiallyBounded.id)))
  refine ⟨a,d₁,d₂,ha2,fun k B hB => ?_⟩
  filter_upwards [hclock k, had, hΔ, eventually_word_stage_le B 0,
    eventually_ge_atTop (2^(E.extra+2))] with n time adviceFits cutFits word hn
  have hr' : addressWidth B n ≤ B*(n.log2+1) := Nat.mul_le_mul_left _ (clog_le_log2_succ n)
  have hw := (word _ 0 hr' (by simp)).1
  dsimp only at cutFits ⊢
  refine ⟨time, adviceFits, by omega, ?_⟩
  constructor
  · have hg : 2 ≤ addressWidth B n + 10 := by omega
    exact (by decide : 2 ≤ 2^4).trans (Nat.pow_le_pow_left hg _)
  · have he : E.extra+2 ≤ n.log2 := (Nat.le_log2 (by have := Nat.two_pow_pos (E.extra+2); omega)).mpr hn
    have h₀ := log2_le_addressWidth hB n
    have h₁ : addressWidth B n + 10 ≤ (addressWidth B n + 10)^4 := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < addressWidth B n + 10) (by decide : 1 ≤ 4)
    exact (he.trans (h₀.trans ((by omega : addressWidth B n ≤ addressWidth B n + 10).trans h₁))).trans Nat.lt_two_pow_self.le
  · have := Nat.mul_le_mul_left (fieldWords (radius n (2*n^a))) hw
    omega

end DiagonalClock

end VPVNP
end Computability
end OAI
