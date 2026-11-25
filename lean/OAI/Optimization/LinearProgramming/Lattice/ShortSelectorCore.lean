import OAI.Optimization.LinearProgramming.Lattice.DirichletReduction
import OAI.Optimization.LinearProgramming.Lattice.LLLScale
import OAI.Optimization.LinearProgramming.Lattice.Precision

/-! Compute the common denominator and numerators directly from the first LLL output row. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

/-- Rational input to the graph-lattice reduction. -/
def rationalGraphMatrix {p : ℕ} (α : ℚ) (u : Fin p → ℚ) : Matrix (Fin (p+1)) (Fin (p+1)) ℚ :=
  Fin.cons (Fin.cons α u) (fun i ↦ Fin.cons 0 (fun j ↦ if i = j then -1 else 0))

theorem rationalGraphMatrix_rows {p : ℕ} (α : ℚ) (u : Fin p → ℚ) :
    (fun i ↦ euclideanRow (rationalGraphMatrix α u i)) = graphGenerators (α : ℝ) (fun i ↦ (u i : ℝ)) := by
  funext i
  ext j
  refine Fin.cases ?_ (fun t ↦ ?_) i <;> refine Fin.cases ?_ (fun s ↦ ?_) j
  all_goals simp [rationalGraphMatrix, euclideanRow, graphGenerators, PiLp.toLp_apply, apply_ite]

/-- Read the integer `q` from the first coordinate and recover `z` from each subsequent one.
The sign normalization guarantees a positive denominator for a nonzero sufficiently short row. -/
def decodeGraphRow {p : ℕ} (α : ℚ) (u : Fin p → ℚ) (r : Fin (p+1) → ℚ) : ℕ × (Fin p → ℤ) :=
  let q := (r 0 / α).num
  let z := fun i ↦ ((q : ℚ) * u i - r i.succ).num
  (q.natAbs, fun i ↦ if 0 ≤ q then z i else -z i)

private theorem decodeGraphRow_eq {p : ℕ} (α : ℚ) (ha : α ≠ 0) (u : Fin p → ℚ)
    (r : Fin (p+1) → ℚ) (q : ℤ) (z : Fin p → ℤ) (h0 : r 0 = α*q)
    (hs : ∀ i, r i.succ = q*u i - z i) :
    decodeGraphRow α u r = (q.natAbs, fun i ↦ if 0 ≤ q then z i else -z i) := by
  simp [decodeGraphRow, h0, hs, ha, mul_div_cancel_left₀]

/-- The denominator parameter in the sign-oracle algorithm dominates the LLL loss and
`8pM`, the required inverse approximation error. -/
theorem searchDenominator_ge_short_grid (p M : ℕ) :
    2^(p+1) * (p+1) * (8*p*M) ≤ searchDenominator p M := by
  calc
    _ ≤ 2^(p+1) * 2^(p+1) * (2^3 * 2^p * 2^M.size) := Nat.mul_le_mul
      (Nat.mul_le_mul_left _ (Nat.lt_two_pow_self.le))
      (Nat.mul_le_mul (Nat.mul_le_mul_left 8 Nat.lt_two_pow_self.le) (Nat.lt_size_self M).le)
    _ = 2^(p+1 + (p+1) + (3+p+M.size)) := by simp only [pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold precisionExponent; omega)

private theorem searchDenominator_graph_norm {p M : ℕ} (hp : 0 < p) (hM : 0 < M) :
    (2 : ℝ) ^ (p+1) * Real.sqrt (p+1) / searchDenominator p M ≤ 1 / (8 * (p : ℝ) * M) := by
  have h := searchDenominator_ge_short_grid p M
  have h' : (2 : ℝ)^(p+1) * (p+1) * (8 * (p : ℝ) * M) ≤ searchDenominator p M := by exact_mod_cast h
  have hroot : Real.sqrt ((p : ℝ)+1) ≤ p+1 := (Real.sqrt_le_left (by positivity)).mpr
    (by nlinarith [sq_nonneg (p : ℝ), Nat.cast_nonneg (α := ℝ) p])
  apply (div_le_div_iff₀ (by exact_mod_cast searchDenominator_pos p M) (by positivity)).mpr
  rw [one_mul]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity)) (by positivity)).trans h'

private theorem euclideanRow_span_le {m n : ℕ} (B A : Matrix (Fin m) (Fin n) ℚ)
    (hs : Submodule.span ℤ (Set.range B) ≤ Submodule.span ℤ (Set.range A)) :
    Submodule.span ℤ (Set.range fun i ↦ euclideanRow (B i)) ≤
      Submodule.span ℤ (Set.range fun i ↦ euclideanRow (A i)) := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hs (Submodule.subset_span (Set.mem_range_self i)))
  change euclideanRow (B i) ∈ _
  rw [← ha, euclideanRow_sum a (fun k : Fin m ↦ (A k : Fin n → ℚ))]
  simp only [Int.cast_smul_eq_zsmul]
  exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

/-- Build the graph input, run the supplied rational row reduction, and decode its first row. -/
def shortSelectorWith {p : ℕ}
    (reduce : Matrix (Fin (p+1)) (Fin (p+1)) ℚ → Matrix (Fin (p+1)) (Fin (p+1)) ℚ)
    (M : ℕ) (u : Fin p → ℚ) : ℕ × (Fin p → ℤ) :=
  let α := 1 / (searchDenominator p M : ℚ) ^ (p+1)
  decodeGraphRow α u (reduce (rationalGraphMatrix α u) 0)

/-- The first row selected by reduction satisfies the exact denominator and error contract
of the sign-rounding algorithm for every rational input vector. -/
theorem shortSelectorWith_correct {p M : ℕ} (hp : 0 < p) (hM : 0 < M)
    (reduce : Matrix (Fin (p+1)) (Fin (p+1)) ℚ → Matrix (Fin (p+1)) (Fin (p+1)) ℚ)
    (hReduce : ∀ A, LinearIndependent ℝ (fun i ↦ euclideanRow (A i)) →
      LLLReduced (fun i ↦ euclideanRow (reduce A i)) ∧
      Submodule.span ℤ (Set.range (reduce A)) = Submodule.span ℤ (Set.range A))
    (u : Fin p → ℚ) :
    0 < (shortSelectorWith reduce M u).1 ∧ (shortSelectorWith reduce M u).1 ≤ searchDenominator p M ^ (p+1) ∧
      ∀ i, |((shortSelectorWith reduce M u).1 : ℚ) * u i - (shortSelectorWith reduce M u).2 i| ≤
        1 / (8 * (p : ℚ) * M) := by
  let Q := searchDenominator p M
  let α : ℚ := 1 / (Q : ℚ)^(p+1)
  let A := rationalGraphMatrix α u
  let B := reduce A
  let b := fun i ↦ euclideanRow (B i)
  have hQ : 0 < Q := searchDenominator_pos p M
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hα : 0 < α := by dsimp [α]; positivity
  have hαr : (α : ℝ) = 1 / (Q : ℝ)^(p+1) := by simp [α]
  have hA := rationalGraphMatrix_rows α u
  have hi : LinearIndependent ℝ (fun i ↦ euclideanRow (A i)) := by
    rw [hA]; exact graphGenerators_independent (by exact_mod_cast hα.ne') _
  obtain ⟨hr, hs⟩ := hReduce A hi
  have hbi : LinearIndependent ℝ b := independent_of_same_integer_row_lattice hi hs
  have hspan : Submodule.span ℤ (Set.range b) =
      Submodule.span ℤ (Set.range (graphGenerators (1 / (Q : ℝ)^(p+1)) (fun i ↦ (u i : ℝ)))) := by
    rw [← hαr, ← hA]
    exact le_antisymm (euclideanRow_span_le B A hs.le) (euclideanRow_span_le A B hs.ge)
  have hvec := (mem_graphLattice_iff _ _ (b 0)).mp (hspan ▸ Submodule.subset_span (Set.mem_range_self 0))
  obtain ⟨q,z,hvec⟩ := hvec
  have hnorm := (graph_reduced_first_short hQ (fun i ↦ (u i : ℝ)) b hbi hr hspan).trans (searchDenominator_graph_norm hp hM)
  have hne := hbi.ne_zero 0
  have hthreshold : 1 / (8 * (p : ℝ) * M) < 1 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [mul_le_mul hp' hM' (by positivity) (by positivity)]
  rw [hvec] at hnorm hne
  have hqn := graphVector_q_ne_zero_of_norm_lt_one hne (hnorm.trans_lt hthreshold)
  have h0 : B 0 0 = α * q := by
    have hg := congrArg (fun x : EuclideanSpace ℝ (Fin (p+1)) ↦ x 0) hvec
    change ((B 0 0 : ℚ) : ℝ) = _ at hg
    rw [graphVector_zero_coord, ← hαr] at hg
    exact Rat.cast_injective (α := ℝ) (by simpa using hg)
  have hcoord (i : Fin p) : B 0 i.succ = q * u i - z i := by
    have hg := congrArg (fun x : EuclideanSpace ℝ (Fin (p+1)) ↦ x i.succ) hvec
    change ((B 0 i.succ : ℚ) : ℝ) = _ at hg
    rw [graphVector_succ_coord] at hg
    exact Rat.cast_injective (α := ℝ) (by simpa using hg)
  change 0 < (decodeGraphRow α u (B 0)).1 ∧ _
  change 0 < (decodeGraphRow α u (B 0)).1 ∧ (decodeGraphRow α u (B 0)).1 ≤ Q^(p+1) ∧
    ∀ i, |((decodeGraphRow α u (B 0)).1 : ℚ) * u i - (decodeGraphRow α u (B 0)).2 i| ≤ _
  rw [decodeGraphRow_eq α hα.ne' u _ q z h0 hcoord]
  refine ⟨Int.natAbs_pos.mpr hqn, ?_, ?_⟩
  · have hh := (PiLp.norm_apply_le (graphVector (1/(Q : ℝ)^(p+1)) (fun i ↦ (u i : ℝ)) q z) 0).trans hnorm
    have hg : |(q : ℝ)| / (Q : ℝ)^(p+1) ≤ 1 := by
      apply le_trans _ hthreshold.le
      simpa [Real.norm_eq_abs, abs_mul, abs_of_pos hQr, div_eq_mul_inv, mul_comm] using hh
    have hn : (q.natAbs : ℝ) ≤ (Q : ℝ)^(p+1) := by
      simpa [Nat.cast_natAbs, Int.cast_abs] using (div_le_iff₀ (by positivity)).mp hg
    exact_mod_cast hn
  · intro i
    have hh := (PiLp.norm_apply_le (graphVector (1/(Q : ℝ)^(p+1)) (fun t ↦ (u t : ℝ)) q z) i.succ).trans hnorm
    have hrat : |(q : ℚ) * u i - z i| ≤ 1 / (8 * (p : ℚ) * M) := by
      apply (Rat.cast_le (K := ℝ)).mp
      simpa [Real.norm_eq_abs] using hh
    change |(q.natAbs : ℚ) * u i - ((if 0 ≤ q then z i else -z i : ℤ) : ℚ)| ≤ _
    rw [Nat.cast_natAbs, Int.cast_abs]
    by_cases h : 0 ≤ q
    · simpa [h, abs_of_nonneg (show 0 ≤ (q : ℚ) by exact_mod_cast h)] using hrat
    · simpa only [h, ite_false, Int.cast_neg, abs_of_neg (show (q : ℚ) < 0 by exact_mod_cast lt_of_not_ge h),
        neg_mul, neg_sub_neg, abs_sub_comm (z i : ℚ)] using hrat

end Lattice
end LinearProgramming
end Optimization
end OAI
