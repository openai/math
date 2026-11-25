import OAI.Optimization.LinearProgramming.Lattice.Dirichlet
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The graph lattice used to obtain simultaneous rational approximations in Appendix A. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

/-- A graph lattice point has a distinguished coordinate `αq` followed by `q u - z`. -/
noncomputable def graphVector {p : ℕ} (α : ℝ) (u : Fin p → ℝ) (q : ℤ) (z : Fin p → ℤ) :
    EuclideanSpace ℝ (Fin (p + 1)) :=
  WithLp.toLp 2 (Fin.cons (α * q) (fun i ↦ q * u i - z i))

@[simp] theorem graphVector_zero_coord {p : ℕ} (α : ℝ) (u : Fin p → ℝ) (q : ℤ) (z : Fin p → ℤ) :
    graphVector α u q z 0 = α * q := rfl

@[simp] theorem graphVector_succ_coord {p : ℕ} (α : ℝ) (u : Fin p → ℝ) (q : ℤ) (z : Fin p → ℤ) (i : Fin p) :
    graphVector α u q z i.succ = q * u i - z i := rfl

/-- A nonzero graph point with `q = 0` has norm at least one. -/
theorem graphVector_q_ne_zero_of_norm_lt_one {p : ℕ} {α : ℝ} {u : Fin p → ℝ}
    {q : ℤ} {z : Fin p → ℤ} (hne : graphVector α u q z ≠ 0)
    (hn : ‖graphVector α u q z‖ < 1) : q ≠ 0 := by
  intro hq
  subst q
  apply hne
  ext j
  refine Fin.cases (by simp) (fun i ↦ ?_) j
  have h : |((z i : ℤ) : ℝ)| < 1 := by
    simpa using (PiLp.norm_apply_le (graphVector α u 0 z) i.succ).trans_lt hn
  have h' : |z i| < (1 : ℤ) := by exact_mod_cast h
  have hz : z i = 0 := by rw [abs_lt] at h'; omega
  simp [hz]

/-- The pigeonhole point gives the Euclidean (rather than only coordinatewise) short-vector bound. -/
theorem graph_short_witness {p Q : ℕ} (hQ : 0 < Q) (u : Fin p → ℝ) :
    let α := 1 / (Q : ℝ) ^ (p + 1)
    ∃ (q : ℕ) (z : Fin p → ℤ), 0 < q ∧ q ≤ Q ^ p ∧ graphVector α u q z ≠ 0 ∧
      ‖graphVector α u q z‖ ≤ Real.sqrt (p + 1) / Q := by
  intro α
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨q, hq, hbound, z, hz⟩ := simultaneous_dirichlet hQ u
  have hqr : (q : ℝ) ≤ (Q : ℝ)^p := by exact_mod_cast hbound
  have hfirst : α * q ≤ 1 / (Q : ℝ) := by
    calc
      α * q ≤ α * (Q : ℝ) ^ p := mul_le_mul_of_nonneg_left hqr hα.le
      _ = _ := by dsimp [α]; rw [pow_succ]; field_simp
  refine ⟨q, z, hq, hbound, ?_, ?_⟩
  · intro h
    have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin (p + 1)) ↦ x 0) h
    have hg : 0 < α * (q : ℝ) := mul_pos hα (Nat.cast_pos.mpr hq)
    simp [hg.ne'] at h0
  · let g := graphVector α u q z
    have hcoord (j : Fin (p + 1)) : ‖g j‖ ≤ 1 / (Q : ℝ) := by
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · simpa [g, Real.norm_eq_abs, abs_of_pos hα] using hfirst
      · simpa [g, Real.norm_eq_abs] using hz i
    rw [EuclideanSpace.norm_eq]
    calc
      _ ≤ Real.sqrt (∑ _ : Fin (p+1), (1 / (Q : ℝ)) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hcoord j) 2)
      _ = _ := by simp [nsmul_eq_mul, Real.sqrt_mul (show (0 : ℝ) ≤ p + 1 by positivity),
        div_eq_mul_inv]

/-- Decode a sufficiently short returned graph-lattice point. The sign of the whole point
is flipped if necessary, so the resulting common denominator is positive. -/
theorem decode_short_graphVector {p : ℕ} (u u' : Fin p → ℝ) (q : ℤ) (z : Fin p → ℤ)
    {α ε : ℝ} (hα : 0 < α) (hε : ε ≤ 1) (hu : ∀ i, |u i| ≤ 1)
    (hclose : ∀ i, |u i - u' i| ≤ α) (hne : graphVector α u' q z ≠ 0)
    (hnorm : ‖graphVector α u' q z‖ ≤ ε / 2) :
    ∃ (d : ℕ) (w : Fin p → ℤ), 0 < d ∧ d ≤ 1 / α ∧
      (∀ i, |(d : ℝ) * u i - w i| ≤ ε) ∧ (∀ i, |w i| ≤ (d : ℤ) + 1) := by
  have hq : q ≠ 0 := graphVector_q_ne_zero_of_norm_lt_one hne (hnorm.trans_lt (by linarith))
  have hd : 0 < q.natAbs := Int.natAbs_pos.mpr hq
  have hqa : |(q : ℝ)| * α ≤ ε / 2 := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos hα, mul_comm] using
      (PiLp.norm_apply_le (graphVector α u' q z) 0).trans hnorm
  have hqz (i : Fin p) : |(q : ℝ) * u' i - z i| ≤ ε / 2 := by
    simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le (graphVector α u' q z) i.succ).trans hnorm
  have hqd : ((q.natAbs : ℕ) : ℝ) = |(q : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  let w := fun i ↦ if 0 ≤ q then z i else -(z i)
  have hw (i : Fin p) : |(q.natAbs : ℝ) * u' i - w i| ≤ ε / 2 := by
    rw [hqd]
    by_cases h : 0 ≤ q
    · simp only [w, h, ite_true, abs_of_nonneg (show 0 ≤ (q : ℝ) by exact_mod_cast h)]
      exact hqz i
    · have hneg : (q : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
      simp only [abs_of_neg hneg, w, h, ite_false, Int.cast_neg, neg_mul, neg_sub_neg, abs_sub_comm (z i : ℝ)]
      exact hqz i
  have hacc := simultaneous_approximation_stable u u' w q.natAbs α ε hclose (hqd ▸ hqa) hw
  refine ⟨q.natAbs, w, hd, (le_div_iff₀ hα).mpr ?_, hacc, ?_⟩
  · rw [hqd]; linarith
  · intro i
    have hwi : |(w i : ℝ)| ≤ (q.natAbs : ℝ) + 1 := by
      calc
        |(w i : ℝ)| = |(q.natAbs : ℝ) * u i - ((q.natAbs : ℝ) * u i - w i)| := by ring_nf
        _ ≤ |(q.natAbs : ℝ) * u i| + |(q.natAbs : ℝ) * u i - w i| := abs_sub ..
        _ ≤ (q.natAbs : ℝ) * 1 + ε := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          exact add_le_add (mul_le_mul_of_nonneg_left (hu i) (Nat.cast_nonneg _)) (hacc i)
        _ ≤ _ := by linarith
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [Int.cast_abs, Int.cast_add, Int.cast_natCast, Int.cast_one] using hwi

end Lattice
end LinearProgramming
end Optimization
end OAI
