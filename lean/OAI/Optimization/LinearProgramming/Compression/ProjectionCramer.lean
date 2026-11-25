import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-! Determinant and coordinate height bounds for an integral tight subsystem. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Leibniz expansion separates the dependence on dimension and entry height. -/
theorem det_natAbs_le_factorial_mul_pow (A : Matrix ι ι ℤ) {B : ℕ}
    (hA : ∀ i j, (A i j).natAbs ≤ B) :
    A.det.natAbs ≤ (Fintype.card ι).factorial * B ^ Fintype.card ι := by
  have term (σ : Equiv.Perm ι) :
      |Equiv.Perm.sign σ • ∏ i, A (σ i) i| ≤ (B : ℤ) ^ Fintype.card ι := by
    have hprod : |∏ i, A (σ i) i| ≤ (B : ℤ) ^ Fintype.card ι := by
      rw [Finset.abs_prod]
      calc
        ∏ i, |A (σ i) i| ≤ ∏ _i : ι, (B : ℤ) := by
          apply Finset.prod_le_prod₀
          · intro i _; exact abs_nonneg _
          · intro i _; simpa only [← Int.natCast_natAbs] using (Int.ofNat_le.mpr (hA (σ i) i))
        _ = _ := by simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simpa [h] using hprod
  have hdet : |A.det| ≤ ((Fintype.card ι).factorial : ℤ) * (B : ℤ) ^ Fintype.card ι := by
    rw [Matrix.det_apply]
    exact (Finset.abs_sum_le_sum_abs _ _).trans <| (Finset.sum_le_sum fun σ _ => term σ).trans_eq
      (by simp [Fintype.card_perm])
  exact_mod_cast (show (A.det.natAbs : ℤ) ≤ _ from (Int.natCast_natAbs _).symm ▸ hdet)

/-- Cramer's rule gives quotients of integer determinants in every characteristic-zero field. -/
theorem cramer_coordinate {K : Type*} [Field K] [CharZero K] (A : Matrix ι ι ℤ)
    (b : ι → ℤ) (x : ι → K) (hdet : A.det ≠ 0)
    (hx : (A.map (fun z : ℤ => (z : K))) *ᵥ x = fun i => (b i : K)) (i : ι) :
    x i = (((A.updateCol i b).det : ℤ) : K) / (A.det : K) := by
  let M := A.map (fun z : ℤ => (z : K))
  have h : M.cramer (fun i => (b i : K)) = M.det • x := by
    rw [← hx, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hi := congrFun h i
  rw [Matrix.cramer_apply] at hi
  change (M.updateCol i (fun j => (b j : K))).det = M.det * x i at hi
  have hn : ((A.updateCol i b).det : K) = (M.updateCol i (fun j => (b j : K))).det := by
    rw [Int.cast_det, Matrix.map_updateCol]; rfl
  apply (eq_div_iff (Int.cast_ne_zero.mpr hdet)).2
  rw [hn, hi, Int.cast_det, mul_comm]

/-- Reducing an integer fraction weakly decreases the two magnitudes. -/
theorem reduced_fraction_height (n d : ℤ) (hd : d ≠ 0) :
    let q : ℚ := (n : ℚ) / (d : ℚ)
    q.num.natAbs ≤ n.natAbs ∧ q.den ≤ d.natAbs := by
  rw [← Rat.divInt_eq_div]
  constructor
  · obtain rfl | hn := eq_or_ne n 0
    · simp
    · exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd n hd))
  · apply Nat.le_of_dvd (Int.natAbs_pos.mpr hd)
    simpa only [Int.natAbs_natCast] using (Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd n d))

/-- Each reduced coordinate of a nonsingular integral system has height at most
the factorial of the dimension times the entry bound to that dimension. -/
theorem cramer_reduced_height (A : Matrix ι ι ℤ) (b : ι → ℤ) {B : ℕ}
    (hA : ∀ i j, (A i j).natAbs ≤ B) (hb : ∀ i, (b i).natAbs ≤ B)
    (hdet : A.det ≠ 0) (x : ι → ℚ)
    (hx : (A.map (fun z : ℤ => (z : ℚ))) *ᵥ x = fun i => (b i : ℚ)) (i : ι) :
    (x i).num.natAbs ≤ (Fintype.card ι).factorial * B ^ Fintype.card ι ∧
    (x i).den ≤ (Fintype.card ι).factorial * B ^ Fintype.card ι := by
  rw [cramer_coordinate A b x hdet hx i]
  have hu : ∀ j k, ((A.updateCol i b) j k).natAbs ≤ B := by
    intro j k
    by_cases hk : k = i
    · subst k; simpa using hb j
    · simpa [Matrix.updateCol_ne hk] using hA j k
  exact ⟨(reduced_fraction_height _ _ hdet).1.trans (det_natAbs_le_factorial_mul_pow _ hu),
    (reduced_fraction_height _ _ hdet).2.trans (det_natAbs_le_factorial_mul_pow _ hA)⟩

/-- A whole rational row (including its constant coordinate) can be cleared at
once. Neither bound depends on how many other rows the system has. -/
theorem clear_bounded_row (v : ι → ℚ) {B : ℕ}
    (hn : ∀ i, (v i).num.natAbs ≤ B) (hd : ∀ i, (v i).den ≤ B) :
    ∃ (D : ℕ) (a : ι → ℤ), 0 < D ∧ D ≤ B ^ Fintype.card ι ∧
      ∀ i, (a i : ℚ) = (D : ℚ) * v i ∧ (a i).natAbs ≤ B ^ (Fintype.card ι + 1) := by
  let den := fun i => (v i).den
  let D := ∏ i, den i
  let e := fun i : ι => ∏ j ∈ Finset.univ.erase i, den j
  have he (i : ι) : e i * den i = D := Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  have hD : D ≤ B ^ Fintype.card ι := by
    calc
      D ≤ ∏ _i : ι, B := Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun i _ => hd i)
      _ = _ := by simp
  refine ⟨D, fun i => (e i : ℤ) * (v i).num,
    Finset.prod_pos (fun i _ => Rat.den_pos (v i)), hD, ?_⟩
  intro i
  constructor
  · rw [← he i, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    simp only [den, mul_assoc, Rat.den_mul_eq_num]
  · have hei : e i ≤ D := he i ▸ Nat.le_mul_of_pos_right (e i) (Rat.den_pos (v i))
    simpa only [Int.natAbs_mul, Int.natAbs_natCast, pow_succ] using
      Nat.mul_le_mul (hei.trans hD) (hn i)

/-- A point over a characteristic-zero field cut out by a nonsingular bounded
integer subsystem is the image of a small rational point. -/
theorem exists_rat_of_tight_integer_system {K : Type*} [Field K] [CharZero K]
    (A : Matrix ι ι ℤ) (b : ι → ℤ) {B : ℕ}
    (hA : ∀ i j, (A i j).natAbs ≤ B) (hb : ∀ i, (b i).natAbs ≤ B)
    (hdet : A.det ≠ 0) (x : ι → K)
    (hx : (A.map (fun z : ℤ => (z : K))) *ᵥ x = fun i => (b i : K)) :
    ∃ q : ι → ℚ, ∀ i, (q i : K) = x i ∧
      (q i).num.natAbs ≤ (Fintype.card ι).factorial * B ^ Fintype.card ι ∧
      (q i).den ≤ (Fintype.card ι).factorial * B ^ Fintype.card ι := by
  refine ⟨fun i => ((A.updateCol i b).det : ℚ) / (A.det : ℚ), ?_⟩
  intro i
  refine ⟨?_, ?_, ?_⟩
  · rw [cramer_coordinate A b x hdet hx i]; simp only [Rat.cast_div, Rat.cast_intCast]
  · apply (reduced_fraction_height _ _ hdet).1.trans
    apply det_natAbs_le_factorial_mul_pow
    intro j k
    by_cases hk : k = i
    · subst k; simpa using hb j
    · simpa [Matrix.updateCol_ne hk] using hA j k
  · exact (reduced_fraction_height _ _ hdet).2.trans (det_natAbs_le_factorial_mul_pow _ hA)

/-- For a square rational tight subsystem, rowwise clearing increases the integer
entry bound by a power depending only on the dimension. Every solution over a
characteristic-zero field is thus rational and has the stated reduced height. -/
theorem exists_small_rat_of_tight_system {K : Type*} [Field K] [CharZero K]
    (A : Matrix ι ι ℚ) (b : ι → ℚ) {B : ℕ}
    (hA : ∀ i j, (A i j).num.natAbs ≤ B ∧ (A i j).den ≤ B)
    (hb : ∀ i, (b i).num.natAbs ≤ B ∧ (b i).den ≤ B)
    (hdet : A.det ≠ 0) (x : ι → K)
    (hx : (A.map (fun z : ℚ => (z : K))) *ᵥ x = fun i => (b i : K)) :
    ∃ q : ι → ℚ, ∀ i, (q i : K) = x i ∧
      (q i).num.natAbs ≤ (Fintype.card ι).factorial *
        (B ^ (Fintype.card ι + 2)) ^ Fintype.card ι ∧
      (q i).den ≤ (Fintype.card ι).factorial *
        (B ^ (Fintype.card ι + 2)) ^ Fintype.card ι := by
  classical
  let row (i : ι) : Option ι → ℚ := fun j => j.elim (b i) (A i)
  have hrow (i : ι) (j : Option ι) :
      (row i j).num.natAbs ≤ B ∧ (row i j).den ≤ B := by
    cases j with
    | none => exact hb i
    | some k => exact hA i k
  choose D a hD _ hclear using fun i =>
    clear_bounded_row (row i) (fun j => (hrow i j).1) (fun j => (hrow i j).2)
  let C : Matrix ι ι ℤ := fun i j => a i (some j)
  let d : ι → ℤ := fun i => a i none
  have hcq (i j : ι) : (C i j : ℚ) = (D i : ℚ) * A i j := (hclear i (some j)).1
  have hdq (i : ι) : (d i : ℚ) = (D i : ℚ) * b i := (hclear i none).1
  have hcast : C.map (fun z : ℤ => (z : ℚ)) = Matrix.diagonal (fun i => (D i : ℚ)) * A := by
    ext i j; rw [Matrix.diagonal_mul]; exact hcq i j
  have hCdet : C.det ≠ 0 := by
    intro hz
    have hzq : (C.det : ℚ) = 0 := by exact_mod_cast hz
    rw [Int.cast_det, hcast, Matrix.det_mul, Matrix.det_diagonal] at hzq
    exact (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast (hD i).ne')) hdet) hzq
  have hcK (i j : ι) : (C i j : K) = (D i : K) * (A i j : K) := by
    simpa only [Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast] using congrArg (fun r : ℚ => (r : K)) (hcq i j)
  have hdK (i : ι) : (d i : K) = (D i : K) * (b i : K) := by
    simpa only [Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast] using congrArg (fun r : ℚ => (r : K)) (hdq i)
  have hxC : (C.map (fun z : ℤ => (z : K))) *ᵥ x = (fun i => (d i : K)) := by
    ext i
    have hxi := congrFun hx i
    change (∑ j, (A i j : K) * x j) = (b i : K) at hxi
    change (∑ j, (C i j : K) * x j) = (d i : K)
    simp_rw [hcK, mul_assoc]
    rw [← Finset.mul_sum, hxi, hdK]
  apply exists_rat_of_tight_integer_system C d _ _ hCdet x hxC
  · intro i j
    simpa only [Fintype.card_option, Nat.add_assoc] using (hclear i (some j)).2
  · intro i
    simpa only [Fintype.card_option, Nat.add_assoc] using (hclear i none).2

/-- Clearing the multipliers and all rows on their support simultaneously produces
a bounded integer representative of the weighted row. The support type `κ` can
be much smaller than the family of constraints from which the rows were selected. -/
theorem clear_weighted_rows {κ : Type*} [Fintype κ] [DecidableEq κ]
    (w : κ → ℚ) (V : κ → ι → ℚ) {B : ℕ}
    (hw : ∀ k, (w k).num.natAbs ≤ B ∧ (w k).den ≤ B)
    (hV : ∀ k i, (V k i).num.natAbs ≤ B ∧ (V k i).den ≤ B) :
    ∃ (D : ℕ) (a : ι → ℤ), 0 < D ∧
      D ≤ (B ^ (Fintype.card κ * (Fintype.card ι + 1))) ^ 2 ∧
      ∀ i, (a i : ℚ) = (D : ℚ) * (∑ k, w k * V k i) ∧
        (a i).natAbs ≤ Fintype.card κ *
          (B ^ (Fintype.card κ * (Fintype.card ι + 1) + 1)) ^ 2 := by
  classical
  let v : κ × Option ι → ℚ := fun p => p.2.elim (w p.1) (V p.1)
  have h (p : κ × Option ι) : (v p).num.natAbs ≤ B ∧ (v p).den ≤ B := by
    obtain ⟨k, _ | i⟩ := p
    · exact hw k
    · exact hV k i
  obtain ⟨D, c, hD, hDB, hc⟩ := clear_bounded_row v (fun p => (h p).1) (fun p => (h p).2)
  simp only [Fintype.card_prod, Fintype.card_option] at hDB hc
  refine ⟨D ^ 2, fun i => ∑ k, c (k, none) * c (k, some i), pow_pos hD _,
    Nat.pow_le_pow_left hDB _, ?_⟩
  intro i
  constructor
  · push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [(hc (k, none)).1, (hc (k, some i)).1]
    change (D : ℚ) * w k * ((D : ℚ) * V k i) = (D : ℚ) ^ 2 * (w k * V k i)
    ring
  · apply (Int.natAbs_sum_le _ _).trans
    calc
      ∑ k, (c (k, none) * c (k, some i)).natAbs ≤
          ∑ _k : κ, (B ^ (Fintype.card κ * (Fintype.card ι + 1) + 1)) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        rw [Int.natAbs_mul, pow_two]
        exact Nat.mul_le_mul (hc (k, none)).2 (hc (k, some i)).2
      _ = _ := by simp

/-- The binary logarithm of the Cramer height for cleared rational rows is bounded
by a polynomial in the dimension and in the binary length of the coefficient bound. -/
theorem log2_le_of_cramer_height {h n B : ℕ}
    (hh : h ≤ n.factorial * (B ^ (n + 2)) ^ n) :
    h.log2 ≤ n * n + (B.log2 + 1) * (n + 2) * n := by
  have hf : n.factorial ≤ 2 ^ (n * n) := by
    rw [pow_mul]
    exact n.factorial_le_pow.trans (Nat.pow_le_pow_left n.lt_two_pow_self.le n)
  have hp : h ≤ 2 ^ (n * n + (B.log2 + 1) * (n + 2) * n) := by
    calc
      h ≤ n.factorial * (B ^ (n + 2)) ^ n := hh
      _ ≤ 2 ^ (n * n) * ((2 ^ (B.log2 + 1)) ^ (n + 2)) ^ n :=
        Nat.mul_le_mul hf (Nat.pow_le_pow_left (Nat.pow_le_pow_left B.lt_log2_self.le _) _)
      _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add, Nat.mul_assoc]
  obtain rfl | hz := eq_or_ne h 0
  · simp
  · exact Nat.le_of_lt_succ ((Nat.log2_lt hz).mpr (hp.trans_lt
        (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))))

end Compression
end LinearProgramming
end Optimization
end OAI
