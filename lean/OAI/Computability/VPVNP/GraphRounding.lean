import OAI.Computability.VPVNP.WalkEnergy
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Log

/-!
# Rounding a symmetric stochastic matrix to a regular multigraph

At the end of Section 5.2 of *VP and VNP differ over every field*, arc
multiplicities are rounded up from half the desired degree times each
transition probability. The missing arcs are loops. The normalized walk
of the resulting multigraph preserves at least half of every edge energy.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {ι : Type*} [Fintype ι]

/-- Entries charged one unit of possible rounding error in a row. -/
noncomputable def rowSupport (P : Matrix ι ι ℝ) (i : ι) : Finset ι :=
  Finset.univ.filter fun j ↦ P i j ≠ 0

/-- The integral arc multiplicities before loops are added. -/
noncomputable def ceilingArcs (P : Matrix ι ι ℝ) (h : ℕ) : Matrix ι ι ℕ :=
  fun i j ↦ ⌈(h : ℝ) / 2 * P i j⌉₊

/-- The loss from rounding up is at most the number of nonzero entries. -/
theorem ceilingArcs_row_le (P : Matrix ι ι ℝ) (h : ℕ) (i : ι)
    (hn : ∀ j, 0 ≤ P i j) (hrow : ∑ j, P i j = 1) :
    ((∑ j, ceilingArcs P h i j : ℕ) : ℝ) ≤ (h : ℝ) / 2 + (rowSupport P i).card := by
  classical
  have term (j : ι) : (ceilingArcs P h i j : ℝ) ≤
      (h : ℝ) / 2 * P i j + (if P i j ≠ 0 then 1 else 0) := by
    by_cases hz : P i j = 0
    · simp [ceilingArcs, hz]
    · rw [ite_eq_left hz]
      exact (Nat.ceil_lt_add_one (mul_nonneg (by positivity : (0 : ℝ) ≤ h / 2) (hn j))).le
  have hcard : (∑ j, if P i j ≠ 0 then (1 : ℝ) else 0) = (rowSupport P i).card := by
    simp [rowSupport, Finset.sum_ite]
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ j, ((h : ℝ) / 2 * P i j + if P i j ≠ 0 then 1 else 0) :=
      Finset.sum_le_sum fun j _ ↦ term j
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hrow, mul_one, hcard]

variable [DecidableEq ι]

/-- Padded arc multiplicities. A loop counts as one outgoing arc. -/
noncomputable def roundedArcs (P : Matrix ι ι ℝ) (h : ℕ) : Matrix ι ι ℕ :=
  fun i j ↦ ceilingArcs P h i j + if i = j then h - ∑ k, ceilingArcs P h i k else 0

/-- Rounding and adding loops preserve symmetry. -/
theorem roundedArcs_symm (P : Matrix ι ι ℝ) (h : ℕ)
    (hs : ∀ i j, P i j = P j i) (i j : ι) : roundedArcs P h i j = roundedArcs P h j i := by
  by_cases heq : i = j
  · subst j
    rfl
  · simp [roundedArcs, ceilingArcs, heq, Ne.symm heq, hs i j]

/-- Every row has total degree exactly `h` when its support has size at most `h / 2`. -/
theorem roundedArcs_row_sum (P : Matrix ι ι ℝ) (h : ℕ) (i : ι)
    (hn : ∀ j, 0 ≤ P i j) (hrow : ∑ j, P i j = 1)
    (hsupp : 2 * (rowSupport P i).card ≤ h) : ∑ j, roundedArcs P h i j = h := by
  have hcap : ∑ j, ceilingArcs P h i j ≤ h := by
    have hcast : 2 * ((rowSupport P i).card : ℝ) ≤ h := by exact_mod_cast hsupp
    have hb := ceilingArcs_row_le P h i hn hrow
    exact Nat.cast_le.mp (by linarith only [hb, hcast] :
      ((∑ j, ceilingArcs P h i j : ℕ) : ℝ) ≤ h)
  simpa [roundedArcs, Finset.sum_add_distrib] using Nat.add_sub_of_le hcap

/-- The transition matrix associated to a regular graph's integral arc counts. -/
noncomputable def normalizeArcs (M : Matrix ι ι ℕ) (h : ℕ) : Matrix ι ι ℝ :=
  fun i j ↦ (M i j : ℝ) / h

omit [DecidableEq ι] in
/-- Uniformly choosing one of the `h` outgoing arcs gives a stochastic row. -/
theorem normalizeArcs_row_sum (M : Matrix ι ι ℕ) {h : ℕ} (hh : 0 < h)
    (i : ι) (hrow : ∑ j, M i j = h) : ∑ j, normalizeArcs M h i j = 1 := by
  simp [normalizeArcs, div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, hrow, hh.ne']

/-- Entrywise lower bound on the normalized rounded transition matrix. -/
theorem roundedArcs_entry_ge (P : Matrix ι ι ℝ) {h : ℕ} (hh : 0 < h) (i j : ι) :
    P i j / 2 ≤ normalizeArcs (roundedArcs P h) h i j := by
  have hle : ceilingArcs P h i j ≤ roundedArcs P h i j := Nat.le_add_right _ _
  apply (le_div_iff₀ (Nat.cast_pos.mpr hh : (0 : ℝ) < h)).mpr
  calc
    _ = (h : ℝ) / 2 * P i j := by ring
    _ ≤ (ceilingArcs P h i j : ℝ) := Nat.le_ceil _
    _ ≤ _ := by exact_mod_cast hle

omit [DecidableEq ι] in
/-- Entrywise domination of half of the original walk preserves half of every edge energy. -/
theorem walkEnergy_le_twice_of_half_le {X : Type*} [PseudoMetricSpace X]
    {P Q : Matrix ι ι ℝ} (hhalf : ∀ i j, P i j / 2 ≤ Q i j) (x : ι → X) :
    walkEnergy P x ≤ 2 * walkEnergy Q x := by
  unfold walkEnergy
  simp_rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ by
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    linarith only [hhalf i j]

omit [DecidableEq ι] in
/-- The entrywise energy comparison gives a factor of two in the Poincaré bound. -/
theorem hasPoincareBound_of_half_le {X : Type*} [PseudoMetricSpace X]
    {P Q : Matrix ι ι ℝ} (hhalf : ∀ i j, P i j / 2 ≤ Q i j) {γ : ℝ} (hγ : 0 ≤ γ)
    (hbound : HasPoincareBound X P γ) : HasPoincareBound X Q (2 * γ) := by
  intro x
  calc
    _ ≤ γ * walkEnergy P x := hbound x
    _ ≤ γ * (2 * walkEnergy Q x) :=
      mul_le_mul_of_nonneg_left (walkEnergy_le_twice_of_half_le hhalf x) hγ
    _ = _ := by ring

/-- Rounding a walk with Poincaré bound `γ` costs at most a factor of two. -/
theorem roundedArcs_hasPoincareBound {X : Type*} [PseudoMetricSpace X]
    (P : Matrix ι ι ℝ) {h : ℕ} (hh : 0 < h) {γ : ℝ} (hγ : 0 ≤ γ)
    (hbound : HasPoincareBound X P γ) :
    HasPoincareBound X (normalizeArcs (roundedArcs P h) h) (2 * γ) :=
  hasPoincareBound_of_half_le (roundedArcs_entry_ge P hh) hγ hbound

/-- Simultaneous realization for every metric target of a sparse symmetric stochastic matrix.
The regular degree is a power of two between twice and four times the support bound. -/
theorem exists_regular_rounding (P : Matrix ι ι ℝ) {k : ℕ} (hk : 0 < k)
    (hn : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (hs : ∀ i j, P i j = P j i) (hkrow : ∀ i, (rowSupport P i).card ≤ k) :
    ∃ e : ℕ, 2 * k ≤ 2 ^ e ∧ 2 ^ e ≤ 4 * k ∧
      ∃ M : Matrix ι ι ℕ, (∀ i j, M i j = M j i) ∧ (∀ i, ∑ j, M i j = 2 ^ e) ∧
        (∀ i j, P i j / 2 ≤ normalizeArcs M (2 ^ e) i j) := by
  let e := Nat.log 2 k + 2
  have hl := Nat.lt_pow_succ_log_self (b := 2) (by decide) k
  have hu := Nat.pow_log_le_self 2 hk.ne'
  have hlow : 2 * k ≤ 2 ^ e := by dsimp [e]; rw [pow_add]; rw [pow_succ] at hl; omega
  have hupp : 2 ^ e ≤ 4 * k := by dsimp [e]; rw [pow_add]; omega
  refine ⟨e, hlow, hupp, roundedArcs P (2 ^ e), roundedArcs_symm P _ hs, ?_, ?_⟩
  · exact fun i ↦ roundedArcs_row_sum P _ i (hn i) (hrow i)
      ((Nat.mul_le_mul_left 2 (hkrow i)).trans hlow)
  · exact roundedArcs_entry_ge P (by positivity)

end SpectralGeometry

end VPVNP
end Computability
end OAI
