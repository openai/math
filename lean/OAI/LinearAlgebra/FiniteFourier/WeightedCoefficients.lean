import OAI.LinearAlgebra.SpectralBooks.PolynomialOverhead
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finset.Sort

/-! # Weighted coefficients of powered matrices

A slot is indexed by one matrix entry (an output–input pair). All slots use the same
indeterminate in their power series. A matrix value multiplies under juxtaposing two
arrays on disjoint, arbitrarily interleaved sets of slots.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

open scoped BigOperators
open PowerSeries

variable {K ι : Type*} [Field K]

/-- Restrict a tuple to a subset of its slots in increasing order. -/
def selectSlots {k : ℕ} (s : Finset (Fin k)) (x : Fin k → ι) (j : Fin s.card) : ι :=
  x (s.orderEmbOfFin rfl j)

/-- The tensor power of an array of single-slot values. -/
def slotPower {R : Type*} [CommMonoid R] (a : ι → R) (k : ℕ) (x : Fin k → ι) : R :=
  ∏ t, a (x t)

/-- The value on powered formats. The interleaving law packages multiplicativity and
simultaneous permutation invariance. The scalar law includes the zero scalar. -/
structure TensorValue (K ι : Type*) [Field K] where
  price (k : ℕ) : ((Fin k → ι) → K) → ℝ
  nonneg {k} (a) : 0 ≤ price k a
  zero (k) : price k 0 = 0
  add {k} (a b) : price k (a + b) ≤ price k a + price k b
  scale {k} (c : K) (a) : price k (c • a) ≤ price k a
  interleave {k} (s : Finset (Fin k)) (a : (Fin s.card → ι) → K)
    (b : (Fin sᶜ.card → ι) → K) :
    price k (fun x => a (selectSlots s x) * b (selectSlots sᶜ x)) =
      price s.card a * price sᶜ.card b
  power (a : ι → K) (k : ℕ) : price k (slotPower a k) = price 1 (slotPower a 1) ^ k

/-- The Taylor coefficient of the entry-wise tensor power, indexed by total degree. -/
def powerCoeff (a : ι → PowerSeries K) (k i : ℕ) (x : Fin k → ι) : K :=
  coeff i (slotPower a k x)

/-- A uniform weighted coefficient estimate allowing polynomial overhead in the slot count
and coefficient index. Only indices through `dk` will be used for a degree-`d` polynomial. -/
def WeightedBound (ν : TensorValue K ι) (w L : ℝ) (a : ι → PowerSeries K) : Prop :=
  ∃ q : ℕ, ∀ k i : ℕ, w ^ i * ν.price k (powerCoeff a k i) ≤
    ((k : ℝ) + i + 1) ^ q * L ^ k

theorem TensorValue.price_sum (ν : TensorValue K ι) {k : ℕ} {α : Type*} (s : Finset α)
    (f : α → (Fin k → ι) → K) : ν.price k (∑ t ∈ s, f t) ≤ ∑ t ∈ s, ν.price k (f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ν.zero]
  | insert t s ht ih =>
    simp only [Finset.sum_insert ht]
    exact (ν.add _ _).trans (add_le_add_right ih _)

private theorem slotPower_select {R : Type*} [CommMonoid R] (a : ι → R) {k : ℕ}
    (s : Finset (Fin k)) (x : Fin k → ι) :
    slotPower a s.card (selectSlots s x) = ∏ t ∈ s, a (x t) := by
  rw [← Finset.prod_attach]
  exact (s.orderIsoOfFin rfl).toEquiv.prod_comp (fun t : s => a (x t.val))

private theorem coeff_interleaved (a b : ι → PowerSeries K) {k : ℕ} (i : ℕ)
    (s : Finset (Fin k)) (x : Fin k → ι) :
    coeff i ((∏ t ∈ s, a (x t)) * ∏ t ∈ sᶜ, b (x t)) =
      ∑ t ∈ Finset.antidiagonal i,
        powerCoeff a s.card t.1 (selectSlots s x) *
          powerCoeff b sᶜ.card t.2 (selectSlots sᶜ x) := by
  simp only [coeff_mul, powerCoeff, slotPower_select]

private theorem powerCoeff_add (a b : ι → PowerSeries K) (k i : ℕ) :
    powerCoeff (a + b) k i =
      ∑ s : Finset (Fin k), ∑ t ∈ Finset.antidiagonal i, fun x =>
        powerCoeff a s.card t.1 (selectSlots s x) * powerCoeff b sᶜ.card t.2 (selectSlots sᶜ x) := by
  funext x
  simp only [Finset.sum_apply, powerCoeff, slotPower, Pi.add_apply, Fintype.prod_add, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact coeff_interleaved a b i s x

/-- In a mixed tensor the Cauchy convolution introduces at most one factor `i+1`.
Summing over all partitions of the slots gives the binomial theorem for the bases `L,U`. -/
theorem WeightedBound.add {ν : TensorValue K ι} {w L U : ℝ} {a b : ι → PowerSeries K}
    (ha : WeightedBound ν w L a) (hb : WeightedBound ν w U b)
    (hw : 0 ≤ w) (hL : 0 ≤ L) (hU : 0 ≤ U) : WeightedBound ν w (L + U) (a + b) := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  refine ⟨p + q + 1, fun k i => ?_⟩
  let H := (k : ℝ) + i + 1
  have hH : 0 ≤ H := by positivity
  let mixed (s : Finset (Fin k)) (t : ℕ × ℕ) (x : Fin k → ι) :=
    powerCoeff a s.card t.1 (selectSlots s x) * powerCoeff b sᶜ.card t.2 (selectSlots sᶜ x)
  have hm (s : Finset (Fin k)) (u : ℕ × ℕ) (hu : u ∈ Finset.antidiagonal i) :
      w ^ i * ν.price k (mixed s u) ≤ H ^ (p + q) * (L ^ s.card * U ^ sᶜ.card) := by
    obtain he : u.1 + u.2 = i := Finset.mem_antidiagonal.mp hu
    have hca : s.card ≤ k := (Finset.card_le_univ s).trans_eq (Fintype.card_fin k)
    have hcb : sᶜ.card ≤ k := (Finset.card_le_univ sᶜ).trans_eq (Fintype.card_fin k)
    have ha : (s.card : ℝ) + u.1 + 1 ≤ H := by dsimp [H]; exact_mod_cast (by omega : s.card + u.1 + 1 ≤ k + i + 1)
    have hb : (sᶜ.card : ℝ) + u.2 + 1 ≤ H := by dsimp [H]; exact_mod_cast (by omega : sᶜ.card + u.2 + 1 ≤ k + i + 1)
    have h₁ := (hp s.card u.1).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) ha p) (pow_nonneg hL _))
    have h₂ := (hq sᶜ.card u.2).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hb q) (pow_nonneg hU _))
    dsimp only [mixed]
    rw [ν.interleave, ← he, pow_add, pow_add]
    calc
      _ = (w ^ u.1 * ν.price s.card (powerCoeff a s.card u.1)) *
          (w ^ u.2 * ν.price sᶜ.card (powerCoeff b sᶜ.card u.2)) := by ring
      _ ≤ _ := (mul_le_mul h₁ h₂ (mul_nonneg (pow_nonneg hw _) (ν.nonneg _))
        (mul_nonneg (pow_nonneg hH _) (pow_nonneg hL _))).trans_eq (by ring)
  rw [powerCoeff_add]
  change w ^ i * ν.price k (∑ s, ∑ t ∈ Finset.antidiagonal i, mixed s t) ≤ _
  calc
    _ ≤ w ^ i * ∑ s : Finset (Fin k), ∑ t ∈ Finset.antidiagonal i, ν.price k (mixed s t) :=
      mul_le_mul_of_nonneg_left ((ν.price_sum _ _).trans (Finset.sum_le_sum
        fun s _ => ν.price_sum _ _)) (pow_nonneg hw _)
    _ = ∑ s : Finset (Fin k), ∑ t ∈ Finset.antidiagonal i, w ^ i * ν.price k (mixed s t) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ s : Finset (Fin k), ∑ _t ∈ Finset.antidiagonal i, H ^ (p + q) *
        (L ^ s.card * U ^ sᶜ.card) :=
      Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t ht => hm s t ht
    _ = ((i : ℝ) + 1) * H ^ (p + q) * (L + U) ^ k := by
      simp only [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul, Nat.cast_succ,
        Finset.card_compl, Fintype.card_fin]
      rw [← show ∑ s : Finset (Fin k), L ^ s.card * U ^ (k - s.card) = (L + U) ^ k by
        simpa only [Fintype.card_fin] using Fintype.sum_pow_mul_eq_add_pow (Fin k) L U]
      simp [Finset.mul_sum, mul_assoc]
    _ ≤ _ := by
      change _ ≤ H ^ (p + q + 1) * (L + U) ^ k
      rw [pow_succ, mul_comm (H ^ (p + q)) H]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (show (i : ℝ) + 1 ≤ H by dsimp [H]; linarith [Nat.cast_nonneg (α := ℝ) k]) (pow_nonneg hH _))
        (pow_nonneg (add_nonneg hL hU) _)

private theorem powerCoeff_scalarSeries (B : PowerSeries K) (a : ι → PowerSeries K) (k i : ℕ) :
    powerCoeff (fun z => B * a z) k i =
      ∑ t ∈ Finset.antidiagonal i, coeff t.1 (B ^ k) • powerCoeff a k t.2 := by
  funext x
  simp [powerCoeff, slotPower, Finset.prod_mul_distrib, coeff_mul, smul_eq_mul]

/-- Multiplication by a common scalar series preserves the exponential base on degrees
linear in the slot count. The Cauchy convolution adds one power to the overhead. -/
theorem WeightedBound.scalarSeries {ν : TensorValue K ι} {w L : ℝ} {a : ι → PowerSeries K}
    (h : WeightedBound ν w L a) (hw : 0 ≤ w) (hw' : w ≤ 1) (hL : 0 ≤ L) (B : PowerSeries K) :
    WeightedBound ν w L (fun z => B * a z) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q+1, fun k i => ?_⟩
  let H := (k : ℝ) + i + 1
  have hH : 0 ≤ H := by positivity
  rw [powerCoeff_scalarSeries]
  calc
    _ ≤ w ^ i * ∑ t ∈ Finset.antidiagonal i,
        ν.price k (coeff t.1 (B ^ k) • powerCoeff a k t.2) :=
      mul_le_mul_of_nonneg_left (ν.price_sum _ _) (pow_nonneg hw _)
    _ ≤ ∑ _t ∈ Finset.antidiagonal i, H ^ q * L ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun t ht => ?_
      obtain he : t.1 + t.2 = i := Finset.mem_antidiagonal.mp ht
      have hwt : w ^ i ≤ w ^ t.2 := pow_le_pow_of_le_one hw hw' (by omega)
      have hHt : (k : ℝ) + t.2 + 1 ≤ H := by dsimp [H]; exact_mod_cast (by omega : k+t.2+1 ≤ k+i+1)
      exact (mul_le_mul hwt (ν.scale _ _) (ν.nonneg _) (pow_nonneg hw _)).trans
        ((hq _ _).trans (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hHt _) (pow_nonneg hL _)))
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul, Nat.cast_succ]
      change _ ≤ H ^ (q+1) * L ^ k
      rw [pow_succ, mul_comm (H ^ q) H, mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (show (i : ℝ) + 1 ≤ H by dsimp [H]; linarith [Nat.cast_nonneg (α := ℝ) k])
        (mul_nonneg (pow_nonneg hH _) (pow_nonneg hL _))

private theorem polynomial_eval_bound (p : Polynomial ℝ) :
    ∃ q : ℕ, ∀ k : ℕ, 1 ≤ k → p.eval (k : ℝ) ≤ ((k : ℝ) + 1) ^ q := by
  induction p using Polynomial.induction_on' with
  | monomial n c =>
    obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt (|c|) (show (1 : ℝ) < 2 by norm_num)
    refine ⟨r+n, fun k hk => ?_⟩
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hc : c ≤ ((k : ℝ) + 1)^r :=
      (le_abs_self _).trans (hr.le.trans (pow_le_pow_left₀ (by norm_num) (by linarith) _))
    rw [Polynomial.eval_monomial, pow_add]
    exact mul_le_mul hc (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (by positivity) (by positivity)
  | add p r hp hr =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hr
    refine ⟨max a b + 1, fun k hk => ?_⟩
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ k + 1 := by linarith
    have hp' := (ha k hk).trans (pow_le_pow_right₀ hk1 (le_max_left a b))
    have hr' := (hb k hk).trans (pow_le_pow_right₀ hk1 (le_max_right a b))
    rw [Polynomial.eval_add, pow_succ]
    calc
      _ ≤ 2 * ((k : ℝ) + 1) ^ max a b := by linarith
      _ ≤ _ := by rw [mul_comm]; gcongr; linarith

/-- The manuscript's walk hypothesis, with a polynomial in the nonempty slot count, implies
the uniform weighted bound. The empty tensor product contributes at coefficient zero. -/
theorem weightedBound_of_walk_estimate {ν : TensorValue K ι} {w L : ℝ}
    (a : ι → PowerSeries K) (p : Polynomial ℝ) (hL : 0 ≤ L)
    (h : ∀ k i : ℕ, 1 ≤ k →
      w ^ i * ν.price k (powerCoeff a k i) ≤ p.eval (k : ℝ) * L ^ k) :
    WeightedBound ν w L a := by
  obtain ⟨q, hq⟩ := polynomial_eval_bound p
  refine ⟨q, fun k i => ?_⟩
  cases k with
  | zero =>
    by_cases hi : i = 0
    · subst i
      have he : powerCoeff a 0 0 = slotPower (fun _ : ι => (1 : K)) 0 := by
        funext x
        simp [powerCoeff, slotPower, coeff_one]
      rw [he, ν.power]
      norm_num
    · have he : powerCoeff a 0 i = 0 := by funext x; simp [powerCoeff, slotPower, coeff_one, hi]
      simp [he, ν.zero]
      positivity
  | succ k =>
    apply (h _ _ (by omega)).trans
    exact mul_le_mul_of_nonneg_right ((hq _ (by omega)).trans
      (pow_le_pow_left₀ (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) i]) _))
      (pow_nonneg hL _)

end

end FiniteFourier
end LinearAlgebra
end OAI
