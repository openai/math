import OAI.LinearAlgebra.FiniteFourier.PrimeQuery
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Algebra.MvPolynomial.Degrees

/-! # The bounded-degree predictor for the window of digit counts

For fixed shifts of the prime-order queries, a linear combination of their
powers detects each shifted residue. Coefficient extraction from the integral
binomial series then produces the predictor without division by factorials.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open MvPolynomial
variable {ℓ m : ℕ} [NeZero ℓ] {K : Type*} [CommRing K] {ζ : K}

private abbrev QueryPolynomial (ℓ m : ℕ) (K : Type*) [CommRing K] :=
  MvPolynomial (Fin m × ZMod ℓ) K

def queryPowerValues (hζ : IsPrimitiveRoot ζ ℓ) (k : Fin m → ZMod ℓ) :
    Fin m × ZMod ℓ → K := fun p => digitPhase hζ (p.2 * k p.1)

private def residueIndicator (hζ : IsPrimitiveRoot ζ ℓ) (j : Fin m) (β u : ZMod ℓ) :
    QueryPolynomial ℓ m K :=
  C (Ring.inverse (ℓ : K)) * ∑ a : ZMod ℓ, C (digitPhase hζ (a * (β-u))) *
    (if a = 0 then 1 else X (j,a))

private theorem residueIndicator_degree (hζ : IsPrimitiveRoot ζ ℓ) (j : Fin m) (β u : ZMod ℓ) :
    (residueIndicator hζ j β u).totalDegree ≤ 1 := by
  unfold residueIndicator
  apply (totalDegree_mul ..).trans
  rw [totalDegree_C, zero_add]
  apply totalDegree_finsetSum_le
  intro a _
  apply (totalDegree_mul ..).trans
  rw [totalDegree_C, zero_add]
  cases subsingleton_or_nontrivial K with
  | inl h =>
    simp [Subsingleton.elim (ite _ _ _) (0 : QueryPolynomial ℓ m K)]
  | inr h => split <;> simp

private theorem eval_residueIndicator (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (hu : IsUnit (ℓ : K)) (k : Fin m → ZMod ℓ)
    (j : Fin m) (β u : ZMod ℓ) :
    eval (queryPowerValues hζ k) (residueIndicator hζ j β u) =
      if k j + β = u then 1 else 0 := by
  let e := eval (queryPowerValues hζ k)
  have term (a : ZMod ℓ) :
      e (C (digitPhase hζ (a * (β-u))) * (if a = 0 then 1 else X (j,a))) =
        digitPhase hζ (a * (k j + β-u)) := by
    by_cases ha : a = 0
    · simp [e, ha]
    · simp only [e, ite_eq_right_iff.mpr (fun h => (ha h).elim), map_mul, eval_C, eval_X, queryPowerValues,
        ← AddChar.map_add_eq_mul]
      congr 1
      ring
  change e _ = _
  unfold residueIndicator
  rw [map_mul, map_sum, Finset.sum_congr rfl (fun a _ => term a),
    PrimeSpectrumOrthogonal.sum_eq (hζ := hζ)]
  by_cases h : k j + β = u <;> simp [e, sub_eq_zero, h, Ring.inverse_mul_cancel _ hu]

private def countSeries (hζ : IsPrimitiveRoot ζ ℓ) (j : Fin m) (β : ZMod ℓ) :
    PowerSeries (QueryPolynomial ℓ m K) :=
  PowerSeries.mk fun d => if d = 0 then 1 else
    ∑ u : ZMod ℓ, C ((u.val.choose d : ℕ) : K) * residueIndicator hζ j β u

/-- The shifted count c in the manuscript, formed using the least residues. -/
def shiftedCount (k β : Fin m → ZMod ℓ) : ℕ := ∑ j, (k j + β j).val

private def weightedDegree {σ : Type*} (P : PowerSeries (MvPolynomial σ K)) : Prop :=
  ∀ d, (PowerSeries.coeff d P).totalDegree ≤ d

private theorem weightedDegree_mul {σ : Type*} {P Q : PowerSeries (MvPolynomial σ K)}
    (hP : weightedDegree P) (hQ : weightedDegree Q) : weightedDegree (P * Q) := by
  intro d
  rw [PowerSeries.coeff_mul]
  apply totalDegree_finsetSum_le
  intro ab hab
  exact (totalDegree_mul ..).trans <|
    (Nat.add_le_add (hP ab.1) (hQ ab.2)).trans_eq (Finset.HasAntidiagonal.mem_antidiagonal.mp hab)

private theorem weightedDegree_binomial {σ : Type*} (z : ℤ) :
    weightedDegree (PowerSeries.binomialSeries (MvPolynomial σ K) z) := by
  intro d
  rw [PowerSeries.binomialSeries_coeff, zsmul_eq_mul, mul_one]
  exact (totalDegree_C ((Ring.choose z d : ℤ) : K)).le.trans (Nat.zero_le d)

private theorem weightedDegree_count (hζ : IsPrimitiveRoot ζ ℓ) (j : Fin m) (β : ZMod ℓ) :
    weightedDegree (countSeries hζ j β) := by
  intro d
  rw [countSeries, PowerSeries.coeff_mk]
  split
  · simp
  · apply totalDegree_finsetSum_le
    intro u _
    apply (totalDegree_mul ..).trans
    rw [totalDegree_C, zero_add]
    exact (residueIndicator_degree hζ j β u).trans (by omega)

/-- Coefficient h of the shifted generating series has query degree at most h. -/
private theorem weightedDegree_series (hζ : IsPrimitiveRoot ζ ℓ) (β : Fin m → ZMod ℓ) (u : ℤ) :
    weightedDegree (PowerSeries.binomialSeries (QueryPolynomial ℓ m K) (-u) *
      ∏ j, countSeries hζ j (β j)) := by
  apply weightedDegree_mul (weightedDegree_binomial _)
  apply Finset.prod_induction _ _ (fun _ _ h₁ h₂ => weightedDegree_mul h₁ h₂)
  · simpa using (weightedDegree_binomial (K := K) (σ := Fin m × ZMod ℓ) 0)
  · intro j _
    exact weightedDegree_count hζ j (β j)

private theorem eval_countSeries (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (hu : IsUnit (ℓ : K)) (k β : Fin m → ZMod ℓ) (j : Fin m) :
    PowerSeries.map (eval (queryPowerValues hζ k)) (countSeries hζ j (β j)) =
      PowerSeries.binomialSeries K ((k j + β j).val : ℤ) := by
  ext d
  rw [PowerSeries.coeff_map, countSeries, PowerSeries.coeff_mk,
    PowerSeries.binomialSeries_coeff, Ring.choose_natCast, natCast_zsmul,
    nsmul_eq_mul, mul_one]
  split
  · rename_i hd
    simp [hd]
  · simp only [map_sum, map_mul, eval_C, eval_residueIndicator hζ hu, mul_ite, mul_one, mul_zero]
    simp

/-- A polynomial of degree at most D in the nonconstant powers of the m
queries. The integer window start may be negative. -/
def countPredictor (hζ : IsPrimitiveRoot ζ ℓ) (β : Fin m → ZMod ℓ) (u : ℤ) (D : ℕ) :
    QueryPolynomial ℓ m K :=
  C (digitPhase hζ ((u : ZMod ℓ) - ∑ j, β j)) *
    ∑ h ∈ Finset.range (D+1), C ((ζ-1)^h) * PowerSeries.coeff h
      (PowerSeries.binomialSeries (QueryPolynomial ℓ m K) (-u) * ∏ j, countSeries hζ j (β j))

theorem countPredictor_totalDegree (hζ : IsPrimitiveRoot ζ ℓ) (β : Fin m → ZMod ℓ) (u : ℤ) (D : ℕ) :
    (countPredictor hζ β u D).totalDegree ≤ D := by
  unfold countPredictor
  apply (totalDegree_mul ..).trans
  rw [totalDegree_C, zero_add]
  apply totalDegree_finsetSum_le
  intro h hh
  apply (totalDegree_mul ..).trans
  rw [totalDegree_C, zero_add]
  exact (weightedDegree_series hζ β u h).trans (by simpa using Finset.mem_range.mp hh)


private theorem eval_count_series_product (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (hu : IsUnit (ℓ : K)) (k β : Fin m → ZMod ℓ) (u : ℤ) :
    PowerSeries.map (eval (queryPowerValues hζ k))
      (PowerSeries.binomialSeries (QueryPolynomial ℓ m K) (-u) *
        ∏ j, countSeries hζ j (β j)) =
      PowerSeries.binomialSeries K ((shiftedCount k β : ℤ) - u) := by
  let e := eval (queryPowerValues hζ k)
  have hmap : PowerSeries.map e
      (PowerSeries.binomialSeries (QueryPolynomial ℓ m K) (-u)) =
        PowerSeries.binomialSeries K (-u) := by
    ext t
    simp [PowerSeries.coeff_map, e, zsmul_eq_mul]
  have hprod (s : Finset (Fin m)) : (∏ j ∈ s, PowerSeries.binomialSeries K ((k j + β j).val : ℤ)) =
      PowerSeries.binomialSeries K (∑ j ∈ s, ((k j + β j).val : ℤ)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, PowerSeries.binomialSeries_add, ih]
  rw [map_mul, map_prod, hmap]
  simp_rw [eval_countSeries hζ hu]
  rw [hprod, ← PowerSeries.binomialSeries_add]
  congr 1
  simp [shiftedCount, sub_eq_add_neg, add_comm]

/-- On every frequency whose shifted count lies inside the integer window,
the predictor is the exact product of the query eigenvalues. -/
theorem eval_countPredictor_of_orthogonal (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (hu : IsUnit (ℓ : K)) (k β : Fin m → ZMod ℓ)
    {u : ℤ} {D : ℕ} (hlo : u ≤ shiftedCount k β) (hhi : (shiftedCount k β : ℤ) ≤ u + D) :
    eval (queryPowerValues hζ k) (countPredictor hζ β u D) =
      ∏ j, digitPhase hζ (k j) := by
  let n := ((shiftedCount k β : ℤ) - u).toNat
  have hn : (n : ℤ) = (shiftedCount k β : ℤ) - u := Int.toNat_of_nonneg (sub_nonneg.mpr hlo)
  have hD : n ≤ D := by omega
  let P := PowerSeries.binomialSeries (QueryPolynomial ℓ m K) (-u) * ∏ j, countSeries hζ j (β j)
  have hcoeff (d : ℕ) : eval (queryPowerValues hζ k) (PowerSeries.coeff d P) =
      (n.choose d : K) := by
    rw [← PowerSeries.coeff_map]
    dsimp only [P]
    rw [eval_count_series_product hζ hu, ← hn, PowerSeries.binomialSeries_coeff,
      Ring.choose_natCast, natCast_zsmul, nsmul_eq_mul, mul_one]
  have hsum : ∑ h ∈ Finset.range (D+1), (ζ-1)^h * (n.choose h : K) = ζ^n := by
    calc
      _ = ∑ h ∈ Finset.range (n+1), (ζ-1)^h * (n.choose h : K) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro i _ hi
        simp [Nat.choose_eq_zero_of_lt (by simpa using hi : n < i)]
      _ = ((ζ-1)+1)^n := by rw [add_pow]; simp
      _ = _ := by rw [sub_add_cancel]
  change eval _ (C _ * ∑ h ∈ Finset.range (D+1), C _ * PowerSeries.coeff h P) = _
  simp only [map_mul, map_sum, eval_C, hcoeff, hsum]
  have hphase : digitPhase hζ (n : ZMod ℓ) = ζ^n := AddChar.zmodChar_apply' _ _
  have hprod (s : Finset (Fin m)) : ∏ j ∈ s, digitPhase hζ (k j) = digitPhase hζ (∑ j ∈ s, k j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, AddChar.map_add_eq_mul, ih]
  rw [← hphase, ← AddChar.map_add_eq_mul, hprod]
  congr 1
  have hz : (n : ZMod ℓ) = (shiftedCount k β : ZMod ℓ) - (u : ZMod ℓ) := by
    exact_mod_cast congrArg (fun t : ℤ => (t : ZMod ℓ)) hn
  rw [hz]
  simp [shiftedCount, Finset.sum_add_distrib]

/-- Field specialization of the normalized predictor identity. -/
theorem eval_countPredictor {F : Type*} [Field F] {ω : F} (hω : IsPrimitiveRoot ω ℓ)
    (k β : Fin m → ZMod ℓ) {u : ℤ} {D : ℕ} (hlo : u ≤ shiftedCount k β)
    (hhi : (shiftedCount k β : ℤ) ≤ u + D) :
    eval (queryPowerValues hω k) (countPredictor hω β u D) = ∏ j, digitPhase hω (k j) :=
  eval_countPredictor_of_orthogonal hω (isUnit_iff_ne_zero.mpr hω.neZero'.out)
    k β hlo hhi

end

end

end FiniteFourier
end LinearAlgebra
end OAI
