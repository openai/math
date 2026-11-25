import OAI.Optimization.LinearProgramming.Lattice.Bisection

/-! Integer sign queries for the sup-normalized image of a rational matrix (Appendix A). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

private theorem formValue_neg {p : ℕ} (a : Fin p → ℤ) (v : Fin p → ℝ) :
    formValue (-a) v = -formValue a v := by simp [formValue, Finset.sum_neg_distrib]

private theorem formValue_sub {p : ℕ} (a b : Fin p → ℤ) (v : Fin p → ℝ) :
    formValue (a - b) v = formValue a v - formValue b v := by
  simp [formValue, sub_mul, Finset.sum_sub_distrib]

/-- The selected integral row and the queries made so far, in reverse order. -/
structure MaxRowResult (p : ℕ) where
  row : Fin p → ℤ
  queries : List (Fin p → ℤ)

/-- Select and orient a row whose value is the largest absolute coordinate.
Its evaluation needs two integer sign tests per row and no data from the hidden vector. -/
def maxAbsRow {p : ℕ} (oracle : (Fin p → ℤ) → Bool) : List (Fin p → ℤ) → MaxRowResult p
  | [] => ⟨0, []⟩
  | a :: rows =>
    let prev := maxAbsRow oracle rows
    let oriented := if oracle a then a else -a
    let difference := oriented - prev.row
    ⟨if oracle difference then oriented else prev.row, difference :: a :: prev.queries⟩

theorem maxAbsRow_query_count {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (rows : List (Fin p → ℤ)) :
    (maxAbsRow oracle rows).queries.length = 2 * rows.length := by
  induction rows with
  | nil => rfl
  | cons a rows ih => simp [maxAbsRow, ih]; omega

private theorem maxAbsRow_cons_value {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (v : Fin p → ℝ)
    (hOracle : ∀ c, oracle c = true ↔ 0 ≤ formValue c v) (a : Fin p → ℤ) (rows : List (Fin p → ℤ)) :
    formValue (maxAbsRow oracle (a :: rows)).row v =
      max |formValue a v| (formValue (maxAbsRow oracle rows).row v) := by
  let oriented := if oracle a then a else -a
  have ho : formValue oriented v = |formValue a v| := by
    by_cases h : oracle a = true
    · simp [oriented, h, abs_of_nonneg ((hOracle _).mp h)]
    · simp [oriented, h, formValue_neg, abs_of_neg (lt_of_not_ge fun hh ↦ h ((hOracle _).mpr hh))]
  change formValue (if oracle (oriented - _) then oriented else _) v = _
  rw [← ho]
  split
  · rename_i h
    have hh := (hOracle _).mp h
    rw [formValue_sub] at hh
    exact (max_eq_left (sub_nonneg.mp hh)).symm
  · rename_i h
    have hh := lt_of_not_ge fun hh ↦ h ((hOracle _).mpr hh)
    rw [formValue_sub] at hh
    exact (max_eq_right (sub_neg.mp hh).le).symm

private theorem maxAbsRow_le_iff {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (v : Fin p → ℝ)
    (hOracle : ∀ c, oracle c = true ↔ 0 ≤ formValue c v) (rows : List (Fin p → ℤ)) (t : ℝ) :
    formValue (maxAbsRow oracle rows).row v ≤ t ↔ 0 ≤ t ∧ ∀ a ∈ rows, |formValue a v| ≤ t := by
  induction rows with
  | nil => simp [maxAbsRow, formValue]
  | cons a rows ih => rw [maxAbsRow_cons_value oracle v hOracle, max_le_iff, ih]; simp; tauto

/-- The denominator chosen by sign queries is exactly the sup norm of the matrix image. -/
theorem maxAbsRow_value {p n : ℕ} (oracle : (Fin p → ℤ) → Bool) (v : Fin p → ℝ)
    (hOracle : ∀ c, oracle c = true ↔ 0 ≤ formValue c v) (rows : Fin n → Fin p → ℤ) :
    formValue (maxAbsRow oracle (List.ofFn rows)).row v = ‖fun i ↦ formValue (rows i) v‖ := by
  apply le_antisymm
  · apply (maxAbsRow_le_iff oracle v hOracle _ _).mpr
    refine ⟨norm_nonneg _, ?_⟩
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact norm_le_pi_norm (fun j ↦ formValue (rows j) v) i
  · have hh := (maxAbsRow_le_iff oracle v hOracle (List.ofFn rows) _).mp le_rfl
    exact (pi_norm_le_iff_of_nonneg hh.1).mpr fun i ↦ hh.2 _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- A common positive denominator for every row, so comparisons across rows preserve scale. -/
def matrixDenominator {n p : ℕ} (P : Fin n → Fin p → ℚ) : ℕ := ∏ i, ∏ j, (P i j).den

theorem matrixDenominator_pos {n p : ℕ} (P : Fin n → Fin p → ℚ) : 0 < matrixDenominator P :=
  Finset.prod_pos fun i _ ↦ Finset.prod_pos fun j _ ↦ (P i j).den_pos

/-- The integer rows implementing the rational-matrix queries. -/
def integralRows {n p : ℕ} (P : Fin n → Fin p → ℚ) (i : Fin n) (j : Fin p) : ℤ :=
  (matrixDenominator P / (P i j).den : ℕ) * (P i j).num

/-- Clearing all denominators multiplies each coordinate by the *same* integer. -/
theorem integralRows_value {n p : ℕ} (P : Fin n → Fin p → ℚ) (v : Fin p → ℝ) (i : Fin n) :
    formValue (integralRows P i) v = matrixDenominator P * (∑ j, (P i j : ℝ) * v j) := by
  rw [Finset.mul_sum, formValue]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hdiv : (P i j).den ∣ matrixDenominator P := (Finset.dvd_prod_of_mem
    (fun j ↦ (P i j).den) (Finset.mem_univ j)).trans (Finset.dvd_prod_of_mem
      (fun i ↦ ∏ j, (P i j).den) (Finset.mem_univ i))
  have hprod : ((matrixDenominator P / (P i j).den : ℕ) : ℝ) * ((P i j).den : ℝ) = matrixDenominator P :=
    by exact_mod_cast Nat.div_mul_cancel hdiv
  have hden : ((P i j).den : ℝ) ≠ 0 := by exact_mod_cast (P i j).den_ne_zero
  simp only [integralRows, Int.cast_mul, Int.cast_natCast, Rat.cast_def]
  rw [← hprod]
  field_simp

/-- Compute every coordinate of `Pv / ‖Pv‖∞` using only an integer-form sign oracle,
including the all-zero case. The output has an explicit dyadic denominator. -/
def normalizedRowApprox {n p : ℕ} (oracle : (Fin p → ℤ) → Bool) (P : Fin n → Fin p → ℚ)
    (k : ℕ) : Fin n → ℚ :=
  let rows := integralRows P
  let d := (maxAbsRow oracle (List.ofFn rows)).row
  if oracle (-d) then 0 else fun i ↦ (dyadicSearch oracle (rows i) d k).numerator / (2 : ℚ) ^ k

/-- On the all-zero branch every coordinate is exactly zero. Otherwise the ratio is obtained
by dyadic bisection using the maximally oriented row as denominator. -/
theorem normalizedRowApprox_error {n p : ℕ} (oracle : (Fin p → ℤ) → Bool) (v : Fin p → ℝ)
    (hOracle : ∀ c, oracle c = true ↔ 0 ≤ formValue c v) (P : Fin n → Fin p → ℚ) (k : ℕ) :
    let x := fun i ↦ ∑ j, (P i j : ℝ) * v j
    ∀ i, |x i / ‖x‖ - (normalizedRowApprox oracle P k i : ℝ)| ≤ 1 / (2 : ℝ) ^ k := by
  intro x i
  let rows := integralRows P
  let d := (maxAbsRow oracle (List.ofFn rows)).row
  let D : ℝ := matrixDenominator P
  have hD : 0 < D := by dsimp [D]; exact_mod_cast matrixDenominator_pos P
  have hrow (j : Fin n) : formValue (rows j) v = D * x j := integralRows_value P v j
  have hnorm : formValue d v = D * ‖x‖ := by
    rw [show formValue d v = _ from maxAbsRow_value oracle v hOracle rows]
    rw [show (fun j ↦ formValue (rows j) v) = D • x from funext hrow, norm_smul, Real.norm_eq_abs, abs_of_pos hD]
  have htest := hOracle (-d)
  rw [formValue_neg, hnorm] at htest
  change |x i / ‖x‖ - ((if oracle (-d) then 0 else fun j ↦ (dyadicSearch oracle (rows j) d k).numerator / (2 : ℚ) ^ k) i : ℝ)| ≤ _
  split
  · rename_i ht
    have hx : ‖x‖ = 0 := by nlinarith [htest.mp ht, norm_nonneg x]
    simp [hx]
  · rename_i ht
    have hnd : 0 < formValue d v := by rw [hnorm]; exact lt_of_not_ge fun h ↦ ht (htest.mpr (neg_nonneg.mpr h))
    have hbound : |formValue (rows i) v| ≤ formValue d v := by
      rw [maxAbsRow_value oracle v hOracle rows]
      exact norm_le_pi_norm (fun j ↦ formValue (rows j) v) i
    have h := dyadicSearch_ratio_error oracle (rows i) d v hOracle hnd hbound k
    rw [hrow, hnorm, mul_div_mul_left _ _ hD.ne'] at h
    simpa using h

end Lattice
end LinearProgramming
end Optimization
end OAI
