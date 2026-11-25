import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Tactic

/-! # Cartier extraction at a branch

Section 10 of *An explicit VNP family requires superpolynomial border circuit size
over every field* works in a completion κ((s)). We represent a differential
η = f(s) ds by its Laurent coefficient series f(s).
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open HahnSeries
open scoped LaurentSeries PowerSeries

variable {K : Type*} [Field K]

private theorem frobenius_shift (p u : ℕ) [ExpChar K p] (D : LaurentSeries K) :
    D ^ p ^ u =
      single ((p ^ u : ℕ) * D.order : ℤ) 1 *
      ofPowerSeries ℤ K (PowerSeries.map (iterateFrobenius K p u)
        (PowerSeries.expand (p ^ u) (expChar_pow_pos K p u).ne' D.powerSeriesPart)) := by
  rw [PowerSeries.map_iterateFrobenius_expand p (expChar_pos K p).ne', map_pow,
    ← one_pow (p ^ u) (M := K), ← nsmul_eq_mul, ← single_pow, ← mul_pow]
  congr 1
  exact D.single_order_mul_powerSeriesPart.symm

/-- Frobenius raises the coefficient to the same power and multiplies its index by that power. -/
theorem coeff_pow_frobenius_mul (p u : ℕ) [ExpChar K p] (D : LaurentSeries K) (i : ℤ) :
    (D ^ p ^ u).coeff ((p ^ u : ℕ) * i) = D.coeff i ^ p ^ u := by
  let q := p ^ u
  have hq := expChar_pow_pos K p u
  have hq' : 0 < (q : ℤ) := by exact_mod_cast hq
  by_cases h : i < D.order
  · rw [coeff_eq_zero_of_lt_order h, zero_pow hq.ne', coeff_eq_zero_of_lt_order]
    rw [order_pow, nsmul_eq_mul]
    exact mul_lt_mul_of_pos_left h hq'
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, i = D.order + k := ⟨(i - D.order).toNat, by omega⟩
    rw [hk, frobenius_shift p u D, coeff_single_mul, one_mul,
      show ((p ^ u : ℕ) : ℤ) * (D.order + k) - (p ^ u : ℕ) * D.order =
        (↑((p ^ u) * k) : ℤ) by push_cast; ring, ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map, PowerSeries.coeff_expand_mul, LaurentSeries.powerSeriesPart_coeff]
    rfl

/-- All other Laurent coefficients of a Frobenius power vanish. -/
theorem coeff_pow_frobenius_of_not_dvd (p u : ℕ) [ExpChar K p] (D : LaurentSeries K) (i : ℤ)
    (hi : ¬ ((p ^ u : ℕ) : ℤ) ∣ i) : (D ^ p ^ u).coeff i = 0 := by
  by_cases h : i < ((p ^ u : ℕ) : ℤ) * D.order
  · apply coeff_eq_zero_of_lt_order
    simpa [order_pow, nsmul_eq_mul] using h
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, i - ((p ^ u : ℕ) : ℤ) * D.order = k :=
      ⟨(i - ((p ^ u : ℕ) : ℤ) * D.order).toNat, by omega⟩
    have hd : ¬ p ^ u ∣ k := by
      intro hd
      apply hi
      rw [← sub_add_cancel i (((p ^ u : ℕ) : ℤ) * D.order), hk]
      exact dvd_add (Int.natCast_dvd_natCast.mpr hd) (dvd_mul_right _ _)
    rw [frobenius_shift p u D, coeff_single_mul, one_mul, hk, ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map, PowerSeries.coeff_expand_of_not_dvd _ _ _ hd, map_zero]



variable (p u : ℕ) [ExpChar K p] [PerfectRing K p]

/-- The Cartier operator on the coefficients of differentials in κ((s)) ds, for q = pᵘ. -/
noncomputable def cartier (η : LaurentSeries K) : LaurentSeries K :=
  ofSuppBddBelow (fun i : ℤ => (iterateFrobeniusEquiv K p u).symm
    (η.coeff ((p ^ u : ℕ) * i + (p ^ u : ℕ) - 1))) <| by
    refine ⟨min 0 η.order - 1, fun i hi => ?_⟩
    contrapose! hi
    rw [Function.notMem_support, coeff_eq_zero_of_lt_order, map_zero]
    have hq : (1 : ℤ) ≤ ((p ^ u : ℕ) : ℤ) := by exact_mod_cast expChar_pow_pos K p u
    have hi' : i + 1 ≤ 0 := by omega
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq) hi', min_le_right 0 η.order]

/-- The coefficient of sⁱ in the extracted differential. -/
theorem cartier_coeff (η : LaurentSeries K) (i : ℤ) :
    (cartier p u η).coeff i = (iterateFrobeniusEquiv K p u).symm
      (η.coeff ((p ^ u : ℕ) * i + (p ^ u : ℕ) - 1)) := rfl

/-- Residue of the differential η(s) ds at the chosen uniformizer. -/
def res (η : LaurentSeries K) : K := η.coeff (-1)

/-- Cartier extracts the inverse Frobenius of the residue. -/
theorem res_cartier (η : LaurentSeries K) :
    res (cartier p u η) = (iterateFrobeniusEquiv K p u).symm (res η) := by
  simp [res, cartier_coeff]

/-- Multiplication by a q-th power before Cartier becomes ordinary multiplication after it. -/
theorem cartier_pow_mul (D η : LaurentSeries K) :
    cartier p u (D ^ p ^ u * η) = D * cartier p u η := by
  ext k
  let q : ℤ := (p ^ u : ℕ)
  let j : ℤ := q * k + q - 1
  have hq : q ≠ 0 := by dsimp [q]; exact_mod_cast (expChar_pow_pos K p u).ne'
  let e := iterateFrobeniusEquiv K p u
  apply e.injective
  change e (e.symm ((D ^ p ^ u * η).coeff j)) = e ((D * cartier p u η).coeff k)
  rw [e.apply_symm_apply, coeff_mul, coeff_mul, map_sum]
  symm
  have indexEq {a b : ℤ} (hab : a + b = k) :
      j - q * a = q * b + q - 1 := by dsimp [j]; rw [← hab]; ring
  have leftDiv {a : ℤ} (h : (D ^ p ^ u).coeff a ≠ 0) : q ∣ a :=
    by_contra fun hn => h (coeff_pow_frobenius_of_not_dvd p u D a hn)
  apply Finset.sum_nbij' (fun ab : ℤ × ℤ => (q * ab.1, j - q * ab.1))
    (fun ab : ℤ × ℤ => (ab.1 / q, k - ab.1 / q))
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_antidiagonal, mem_support] at hab ⊢
    obtain ⟨ha, hb, hk⟩ := hab
    rw [coeff_pow_frobenius_mul, indexEq hk]
    exact ⟨pow_ne_zero _ ha, fun hz => hb (by rw [cartier_coeff, hz, map_zero]), by
      dsimp [j]; rw [← hk]; ring⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_antidiagonal, mem_support] at hab ⊢
    obtain ⟨ha, hb, h⟩ := hab
    have hqa := Int.mul_ediv_cancel_of_dvd (leftDiv ha)
    have hkb : q * (k - a / q) + q - 1 = b := by
      dsimp [j] at h
      rw [mul_sub, hqa]
      omega
    refine ⟨?_, ?_, by omega⟩
    · rw [← hqa, coeff_pow_frobenius_mul] at ha
      exact fun hz => ha (by rw [hz, zero_pow (expChar_pow_pos K p u).ne'])
    · rw [cartier_coeff, hkb]
      simpa only [map_zero] using e.symm.injective.ne hb
  · rintro ⟨a, b⟩ hab
    have hk := (Finset.mem_antidiagonal.mp hab).2.2
    simp only [Int.mul_ediv_cancel_left _ hq, Prod.mk.injEq, true_and]
    omega
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, _, h⟩ := Finset.mem_antidiagonal.mp hab
    have hqa := Int.mul_ediv_cancel_of_dvd (leftDiv ((mem_support _ _).mp ha))
    simp only [hqa, Prod.mk.injEq, true_and]
    omega
  · rintro ⟨a, b⟩ hab
    have hk := (Finset.mem_antidiagonal.mp hab).2.2
    rw [map_mul, coeff_pow_frobenius_mul, indexEq hk, cartier_coeff]
    change D.coeff a ^ p ^ u * e (e.symm _) = _
    rw [e.apply_symm_apply]

omit [PerfectRing K p] in
/-- If A is regular, its nonconstant part vanishes to positive order. Raising it to
q cancels every pole of the test of order at most q, even when the monomials
which sum to A individually have poles. -/
theorem res_pow_mul_of_regular (A η : LaurentSeries K) (hA : 0 ≤ A.order)
    (hη : -((p ^ u : ℕ) : ℤ) ≤ η.order) :
    res (A ^ p ^ u * η) = A.coeff 0 ^ p ^ u * res η := by
  have : ExpChar (LaurentSeries K) p :=
    expChar_of_injective_ringHom (f := HahnSeries.C) HahnSeries.C_injective p
  let z := A.coeff 0
  let d := A - C z
  have hq := expChar_pow_pos K p u
  have cancel : res (d ^ p ^ u * η) = 0 := by
    by_cases hd : d = 0
    · simp [hd, res, zero_pow hq.ne']
    by_cases he : η = 0
    · simp [he, res]
    have hpos : 1 ≤ d.order := by
      apply (le_order_iff_forall hd).mpr
      intro j hj
      change (A - C z).coeff j = 0
      rw [coeff_sub, C_apply]
      rcases eq_or_lt_of_le (show j ≤ 0 by omega) with rfl | hj'
      · simp [z]
      · rw [coeff_eq_zero_of_lt_order (hj'.trans_le hA), coeff_single_of_ne hj'.ne, sub_zero]
    apply coeff_eq_zero_of_lt_order
    rw [order_mul (pow_ne_zero _ hd) he, order_pow, nsmul_eq_mul]
    have hmul := mul_le_mul_of_nonneg_left hpos
      (show 0 ≤ ((p ^ u : ℕ) : ℤ) from Int.natCast_nonneg _)
    linarith
  have hr := sub_pow_expChar_pow (p := p) A (C z) u
  change (d ^ p ^ u * η).coeff (-1) = 0 at cancel
  rw [show d ^ p ^ u = A ^ p ^ u - C (z ^ p ^ u) by simpa [d] using hr,
    sub_mul, coeff_sub, C_apply, coeff_single_mul] at cancel
  simpa only [res, sub_zero, z] using sub_eq_zero.mp cancel

/-- Absolute trace of the Laurent residue, the functional used for the pins. -/
noncomputable def tracedRes [Algebra (ZMod p) K] (η : LaurentSeries K) : ZMod p :=
  Algebra.trace (ZMod p) K (res η)

/-- Absolute trace is invariant under the inverse coefficient Frobenius. -/
theorem tracedRes_cartier [Algebra (ZMod p) K] (η : LaurentSeries K) :
    tracedRes p (cartier p u η) = tracedRes p η := by
  rw [tracedRes, res_cartier, tracedRes]
  let e := (iterateFrobeniusEquiv K p u).symm
  have he : ∀ x : ZMod p, e (algebraMap (ZMod p) K x) = algebraMap (ZMod p) K x :=
    DFunLike.congr_fun (RingHom.ext_zmod (e.toRingHom.comp (algebraMap _ _)) (algebraMap _ _))
  exact Algebra.trace_eq_of_algEquiv (AlgEquiv.ofRingEquiv he) (res η)

/-- In the prime field the complete regular sum acts on every traced residue test
by its special value. This is the scalar equality behind (10.1). -/
theorem tracedRes_mul_cartier_of_regular [Algebra (ZMod p) K] (A η : LaurentSeries K)
    (z : ZMod p) (hz : A.coeff 0 = algebraMap (ZMod p) K z) (hA : 0 ≤ A.order)
    (hη : -((p ^ u : ℕ) : ℤ) ≤ η.order) :
    tracedRes p (A * cartier p u η) = z * tracedRes p η := by
  rw [← cartier_pow_mul, tracedRes_cartier, tracedRes, res_pow_mul_of_regular p u A η hA hη, hz]
  have hpow : (algebraMap (ZMod p) K z) ^ p ^ u = algebraMap (ZMod p) K z :=
    DFunLike.congr_fun (RingHom.ext_zmod
      ((iterateFrobenius K p u).comp (algebraMap (ZMod p) K)) (algebraMap (ZMod p) K)) z
  rw [hpow, ← Algebra.smul_def, map_smul, smul_eq_mul, tracedRes]

end Residue

end BorderVNP
end Computability
end OAI
