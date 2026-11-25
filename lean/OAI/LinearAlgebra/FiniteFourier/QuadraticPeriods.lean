import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic

/-! # The two-orbit quadratic period on a prime axis

For a prime congruent to three modulo four, count ordered pairs consisting
of a nonzero square and a nonsquare with prescribed sum. Computing the
counts over the integers allows the period relation to specialize even
in rings where two fails to be invertible.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators
open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private def residueCount (ε : ℤ) (x : F) : ℤ := if quadraticChar F x = ε then 1 else 0

private def indicatorConvolution (f g : F → ℤ) (t : F) : ℤ := ∑ x, f x * g (t-x)

omit [DecidableEq F] in
private theorem indicatorConvolution_comm (f g : F → ℤ) (t : F) :
    indicatorConvolution f g t = indicatorConvolution g f t := by
  exact Fintype.sum_equiv (Equiv.subLeft t) _ _ (fun x => by simp [Equiv.subLeft, mul_comm])

private theorem doubled_residue_counts (x : F) :
    2 * residueCount 1 x = (1 : MulChar F ℤ) x + quadraticChar F x ∧
    2 * residueCount (-1) x = (1 : MulChar F ℤ) x - quadraticChar F x := by
  by_cases hx : x = 0
  · simp [hx, residueCount, MulChar.map_zero]
  rcases quadraticChar_dichotomy hx with h | h <;>
    norm_num [residueCount, h, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]

private theorem four_mixed_pairs (t : F) :
    4 * indicatorConvolution (residueCount 1) (residueCount (-1)) t =
      indicatorConvolution (1 : MulChar F ℤ) (1 : MulChar F ℤ) t -
      indicatorConvolution (quadraticChar F) (quadraticChar F) t := by
  have heq : 4 * indicatorConvolution (residueCount 1) (residueCount (-1)) t =
      indicatorConvolution (1 : MulChar F ℤ) (1 : MulChar F ℤ) t -
      indicatorConvolution (1 : MulChar F ℤ) (quadraticChar F) t +
      indicatorConvolution (quadraticChar F) (1 : MulChar F ℤ) t -
      indicatorConvolution (quadraticChar F) (quadraticChar F) t := by
    unfold indicatorConvolution
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro x _
    have h := congrArg₂ (· * ·) (doubled_residue_counts x).1 (doubled_residue_counts (t-x)).2
    linear_combination h
  rw [indicatorConvolution_comm (quadraticChar F) (1 : MulChar F ℤ)] at heq
  linarith only [heq]

omit [DecidableEq F] in
private theorem mulChar_convolution (χ φ : MulChar F ℤ) {t : F} (ht : t ≠ 0) :
    indicatorConvolution χ φ t = (χ t * φ t) * jacobiSum χ φ := by
  simp only [indicatorConvolution, jacobiSum, mul_sum]
  symm
  apply Fintype.sum_equiv (Equiv.mulLeft₀ t ht)
  intro y
  change χ t * φ t * (χ y * φ (1-y)) = χ (t*y) * φ (t - t*y)
  rw [show t - t*y = t*(1-y) by ring, map_mul, map_mul]
  ring

private theorem trivial_convolution_zero :
    indicatorConvolution (1 : MulChar F ℤ) (1 : MulChar F ℤ) 0 = (Fintype.card F : ℤ)-1 := by
  have h (x : F) : (1 : MulChar F ℤ) x * (1 : MulChar F ℤ) (0-x) = (1 : MulChar F ℤ) x := by
    by_cases hx : x = 0
    · simp [hx, MulChar.map_zero]
    · simp [MulChar.one_apply (isUnit_iff_ne_zero.mpr hx),
        MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hx))]
  simp only [indicatorConvolution, h, MulChar.sum_one_eq_card_units, Fintype.card_units,
    Nat.cast_sub Fintype.card_pos, Nat.cast_one]

private theorem quadratic_convolution_zero (hneg : quadraticChar F (-1) = -1) :
    indicatorConvolution (quadraticChar F) (quadraticChar F) 0 = -((Fintype.card F : ℤ) - 1) := by
  have h (x : F) : quadraticChar F x * quadraticChar F (0-x) = -(1 : MulChar F ℤ) x := by
    by_cases hx : x = 0
    · simp [hx, MulChar.map_zero]
    · rw [zero_sub, ← neg_one_mul x, map_mul, hneg, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
      nlinarith only [quadraticChar_sq_one hx]
  simp only [indicatorConvolution, h, sum_neg_distrib, MulChar.sum_one_eq_card_units,
    Fintype.card_units, Nat.cast_sub Fintype.card_pos, Nat.cast_one]

/-- Integer multiplicity of a sum of one nonzero square and one nonsquare
in a prime field congruent to three modulo four. -/
theorem square_nonsquare_sum_count {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) (t : ZMod p) :
    (∑ x : ZMod p, (if quadraticChar (ZMod p) x = 1 then 1 else 0 : ℤ) *
      (if quadraticChar (ZMod p) (t-x) = -1 then 1 else 0 : ℤ)) =
      if t = 0 then ((p-1)/2 : ℕ) else ((p-3)/4 : ℕ) := by
  let F := ZMod p
  have hneg : quadraticChar F (-1) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr (by
    rw [FiniteField.isSquare_neg_one_iff]
    simpa [F, ZMod.card] using hp)
  have h := four_mixed_pairs t
  change indicatorConvolution (residueCount 1) (residueCount (-1)) t = _
  by_cases ht : t = 0
  · subst t
    rw [trivial_convolution_zero, quadratic_convolution_zero hneg, ZMod.card] at h
    simp only [ite_true]
    omega
  · rw [mulChar_convolution _ _ ht, mulChar_convolution _ _ ht, jacobiSum_one_one,
      MulChar.one_apply (isUnit_iff_ne_zero.mpr ht), one_mul,
      ← pow_two, quadraticChar_sq_one ht, one_mul] at h
    have hneq := quadraticChar_ne_one (F := F) (by rw [show ringChar F = p from ZMod.ringChar_zmod_n p]; omega)
    have hj := jacobiSum_nontrivial_inv hneq
    rw [(quadraticChar_isQuadratic F).inv, hneg] at hj
    rw [hj, ZMod.card] at h
    simp only [ite_eq_right ht]
    omega

variable {R : Type*} [CommRing R]

/-- Sum of the powers on the square (`ε=1`) or nonsquare (`ε=-1`) orbit. -/
def quadraticPeriod (ψ : AddChar F R) (ε : ℤ) : R :=
  ∑ x, (residueCount ε x : R) * ψ x

theorem quadraticPeriod_eq_sum (ψ : AddChar F R) (ε : ℤ) :
    quadraticPeriod ψ ε = ∑ x, if quadraticChar F x = ε then ψ x else 0 := by
  simp [quadraticPeriod, residueCount, apply_ite, ite_mul]

omit [DecidableEq F] in
private theorem period_convolution (ψ : AddChar F R) (f g : F → ℤ) :
    (∑ x, (f x : R)*ψ x)*(∑ y, (g y : R)*ψ y) =
      ∑ t, (indicatorConvolution f g t : R)*ψ t := by
  rw [sum_mul_sum]
  have hfirst (x : F) :
      (∑ y, (f x : R)*ψ x*((g y : R)*ψ y)) =
      ∑ t, ((f x : R)*g (t-x))*ψ t := by
    apply Fintype.sum_equiv (Equiv.addLeft x)
    intro y
    change (f x : R)*ψ x*((g y : R)*ψ y) = (f x : R)*g (x+y-x)*ψ (x+y)
    rw [add_sub_cancel_left, AddChar.map_add_eq_mul]
    ring
  simp_rw [hfirst]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  simp only [indicatorConvolution, Int.cast_sum, Int.cast_mul, sum_mul]

/-- The two nonzero-residue period sums add to `-1` if all `p` powers sum to zero. -/
theorem quadraticPeriod_add (ψ : AddChar F R) (hψ : ∑ x, ψ x = 0) :
    quadraticPeriod ψ 1 + quadraticPeriod ψ (-1) = -1 := by
  have hc (x : F) : ((residueCount 1 x : R) + residueCount (-1) x) =
      if x = 0 then 0 else 1 := by
    by_cases hx : x = 0
    · simp [residueCount, hx]
    rcases quadraticChar_dichotomy hx with h | h <;> norm_num [residueCount, h, hx]
  rw [quadraticPeriod, quadraticPeriod, ← sum_add_distrib]
  simp_rw [← add_mul, hc]
  have ht : (∑ x, (if x = 0 then (0:R) else 1) * ψ x) =
      (∑ x, ψ x) - ∑ x, if x = 0 then ψ x else 0 := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro x _
    by_cases hx : x = 0 <;> simp [hx]
  rw [ht, hψ]
  simp

/-- The product `U τ(U)` of the two Gaussian periods is `(p+1)/4` in
any commutative coefficient ring. No division by two in that ring is used. -/
theorem quadraticPeriod_mul {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (ψ : AddChar (ZMod p) R) (hψ : ∑ x, ψ x = 0) :
    quadraticPeriod ψ 1 * quadraticPeriod ψ (-1) = (((p+1)/4 : ℕ) : R) := by
  let m := (p-3)/4
  let ρ := (p+1)/4
  have hm : (p-1)/2 = ρ+m := by dsimp [ρ,m]; omega
  rw [quadraticPeriod, quadraticPeriod, period_convolution]
  have hc (t : ZMod p) :
      (indicatorConvolution (residueCount 1) (residueCount (-1)) t : R) * ψ t =
      (m : R)*ψ t + (if t = 0 then (ρ : R)*ψ t else 0) := by
    have h := square_nonsquare_sum_count hp t
    change indicatorConvolution (residueCount 1) (residueCount (-1)) t = _ at h
    rw [h]
    by_cases ht : t = 0
    · rw [ite_eq_left ht, ite_eq_left ht, hm, Int.cast_natCast, Nat.cast_add, add_mul, add_comm]
    · rw [ite_eq_right ht, ite_eq_right ht, Int.cast_natCast, add_zero]
  simp_rw [hc]
  rw [sum_add_distrib, ← mul_sum, hψ, mul_zero, zero_add]
  simp [ρ]

/-- The quadratic defining equation in the positive prime-axis algebra. -/
theorem quadraticPeriod_equation {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (ψ : AddChar (ZMod p) R) (hψ : ∑ x, ψ x = 0) :
    (quadraticPeriod ψ 1)^2 + quadraticPeriod ψ 1 + (((p+1)/4 : ℕ) : R) = 0 := by
  have hsum := quadraticPeriod_add ψ hψ
  have hmul := quadraticPeriod_mul hp ψ hψ
  linear_combination (quadraticPeriod ψ 1) * hsum - hmul

section CyclotomicAxis

open Polynomial

variable (R) (p : ℕ) [Fact p.Prime]

theorem primeAxis_power_sum :
    ∑ j ∈ Finset.range p, AdjoinRoot.root (cyclotomic p R) ^ j = 0 := by
  have h := AdjoinRoot.aeval_eq (f := cyclotomic p R) (cyclotomic p R)
  rw [AdjoinRoot.mk_self] at h
  conv at h => lhs; arg 2; rw [cyclotomic_prime R p]
  simpa using h

theorem primeAxis_pow :
    AdjoinRoot.root (cyclotomic p R) ^ p = 1 := by
  have h := geom_sum_mul (AdjoinRoot.root (cyclotomic p R)) p
  rw [primeAxis_power_sum, zero_mul] at h
  exact sub_eq_zero.mp h.symm

/-- Powers of the universal class of `X` in `R[X]/Φₚ`, as an additive
character of the cyclic address group. -/
noncomputable def primeAxisCharacter : AddChar (ZMod p) (AdjoinRoot (cyclotomic p R)) :=
  AddChar.zmodChar p (primeAxis_pow R p)

theorem primeAxisCharacter_sum : ∑ j, primeAxisCharacter R p j = 0 := by
  rw [← (ZMod.finEquiv p).toEquiv.sum_comp (primeAxisCharacter R p)]
  convert primeAxis_power_sum R p using 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  change AdjoinRoot.root (cyclotomic p R) ^ ((ZMod.finEquiv p j).val) = AdjoinRoot.root (cyclotomic p R) ^ j.val
  congr 1
  cases p with
  | zero => cases (Fact.out : Nat.Prime 0).ne_zero rfl
  | succ p => rfl

/-- The prime-axis quadratic relation in the actual quotient `R[X]/Φₚ`,
including coefficient rings of characteristic two. -/
theorem primeAxis_square_period (hp : p % 4 = 3) :
    let U := quadraticPeriod (primeAxisCharacter R p) 1
    U^2 + U + (((p+1)/4 : ℕ) : AdjoinRoot (cyclotomic p R)) = 0 :=
  quadraticPeriod_equation hp _ (primeAxisCharacter_sum R p)

end CyclotomicAxis

end FiniteFourier
end LinearAlgebra
end OAI
