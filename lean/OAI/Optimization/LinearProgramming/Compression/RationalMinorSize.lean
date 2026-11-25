import OAI.Optimization.LinearProgramming.Compression.ProjectionCramer
import OAI.Optimization.LinearProgramming.Specification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators Matrix

/-- A common denominator makes all entries integral simultaneously. The bounds include
matrix sizes zero and one. -/
theorem exists_scaled_integer_matrix {n H : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hnum : ∀ i j, (A i j).num.natAbs ≤ H) (hden : ∀ i j, (A i j).den ≤ H) :
    ∃ (D : ℕ) (C : Matrix (Fin n) (Fin n) ℤ), 0 < D ∧ D ≤ H ^ (n ^ 2) ∧
      (∀ i j, (C i j : ℚ) = (D : ℚ) * A i j) ∧ ∀ i j, (C i j).natAbs ≤ H * D := by
  classical
  let D := ∏ i, ∏ j, (A i j).den
  have hDpos : 0 < D := Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => (A i j).pos
  have hdvd (i j) : (A i j).den ∣ D :=
    (Finset.dvd_prod_of_mem (fun j => (A i j).den) (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ j, (A i j).den) (Finset.mem_univ i))
  have hD : D ≤ H ^ (n ^ 2) := calc
    D ≤ ∏ _i : Fin n, ∏ _j : Fin n, H :=
      Finset.prod_le_prod fun i _ => Finset.prod_le_prod fun j _ => hden i j
    _ = _ := by simp [pow_two, pow_mul]
  let C : Matrix (Fin n) (Fin n) ℤ := fun i j => (A i j).num * (D / (A i j).den : ℕ)
  have hC : ∀ i j, (C i j).natAbs ≤ H * D := by
    intro i j
    simp only [C, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul (hnum i j) (Nat.div_le_self _ _)
  have heq : C.map (fun z : ℤ => (z : ℚ)) = (D : ℚ) • A := by
    ext i j
    change (↑((A i j).num * ((D / (A i j).den : ℕ) : ℤ)) : ℚ) = (D : ℚ) * A i j
    push_cast
    change ((A i j).num : ℚ) * (↑(D / (A i j).den) : ℚ) = D * A i j
    have hprod : (↑(D / (A i j).den) : ℚ) * ((A i j).den : ℚ) = D := by
      exact_mod_cast Nat.div_mul_cancel (hdvd i j)
    calc
      _ = ((A i j).num / ((A i j).den : ℚ)) * (↑(D / (A i j).den) * (A i j).den) := by
        field_simp [Rat.den_nz]
      _ = _ := by rw [Rat.num_div_den, hprod, mul_comm]
  exact ⟨D, C, hDpos, hD, (fun i j => congrFun (congrFun heq i) j), hC⟩

/-- Clearing all input denominators bounds the reduced determinant, including singular matrices. -/
theorem rational_det_height {n H : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hnum : ∀ i j, (A i j).num.natAbs ≤ H) (hden : ∀ i j, (A i j).den ≤ H) :
    A.det.num.natAbs ≤ n.factorial * (H * H ^ (n ^ 2)) ^ n ∧
    A.det.den ≤ (H ^ (n ^ 2)) ^ n := by
  obtain ⟨D, C, hDpos, hD, hcast, hC⟩ := exists_scaled_integer_matrix A hnum hden
  have heq : C.map (fun z : ℤ => (z : ℚ)) = (D : ℚ) • A := Matrix.ext hcast
  have hq : A.det = ((C.det : ℤ) : ℚ) / ((D ^ n : ℕ) : ℤ) := by
    apply (eq_div_iff (by positivity)).2
    rw [Int.cast_det, heq, Matrix.det_smul, Fintype.card_fin, mul_comm]
    norm_cast
  have hred := reduced_fraction_height C.det (((D ^ n : ℕ) : ℤ)) (by positivity)
  have hred' : A.det.num.natAbs ≤ C.det.natAbs ∧ A.det.den ≤ D^n := by
    simpa only [← hq, Int.natAbs_natCast] using hred
  have hCdet := det_natAbs_le_factorial_mul_pow C hC
  rw [Fintype.card_fin] at hCdet
  exact ⟨hred'.1.trans (hCdet.trans (by gcongr)), hred'.2.trans (by gcongr)⟩

/-- A dyadic upper bound controls the integer binary logarithm, including zero. -/
theorem log2_le_of_le_two_pow {x k : ℕ} (h : x ≤ 2 ^ k) : x.log2 ≤ k := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  apply Nat.le_of_lt_succ ((Nat.log2_lt hx).2 ?_)
  rw [pow_succ]; have hp := Nat.two_pow_pos k; omega

/-- A dimension/entry-bit bound on a rational minor in the machine's actual encoding. -/
theorem rational_det_bits {n B : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hbit : ∀ i j, RAM.ratBits (A i j) ≤ B) :
    RAM.ratBits A.det ≤ 3 + n^2 + B*n + 2*B*n^3 := by
  have height (i j : Fin n) : (A i j).num.natAbs ≤ 2 ^ B ∧ (A i j).den ≤ 2 ^ B := by
    have hb := hbit i j
    unfold RAM.ratBits at hb
    constructor
    · exact Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    · exact Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨hnum, hden⟩ := rational_det_height A (fun i j => (height i j).1) (fun i j => (height i j).2)
  have hfac : n.factorial ≤ 2 ^ (n ^ 2) := calc
    n.factorial ≤ n ^ n := n.factorial_le_pow
    _ ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left n.lt_two_pow_self.le _
    _ = 2 ^ (n ^ 2) := by rw [← pow_mul, pow_two]
  have hn : A.det.num.natAbs ≤ 2 ^ (n^2 + (B+B*n^2)*n) := calc
    _ ≤ n.factorial * (2^B * (2^B)^(n^2))^n := hnum
    _ ≤ 2^(n^2) * (2^B * (2^B)^(n^2))^n := Nat.mul_le_mul_right _ hfac
    _ = _ := by rw [← pow_mul, ← pow_add, ← pow_mul, ← pow_add]
  have hd : A.det.den ≤ 2 ^ (B*n^2*n) := by simpa only [← pow_mul] using hden
  unfold RAM.ratBits
  calc
    _ ≤ 3 + (n^2 + (B+B*n^2)*n) + B*n^2*n := by
      exact Nat.add_le_add (Nat.add_le_add_left (log2_le_of_le_two_pow hn) 3)
        (log2_le_of_le_two_pow hd)
    _ = _ := by ring

/-- The sum of binary lengths of the rational entries of an input matrix. -/
def matrixEncodingLength {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) : ℕ :=
  ∑ i, ∑ j, RAM.ratBits (A i j)

theorem matrix_entry_bits_le {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (i : Fin m) (j : Fin d) :
    RAM.ratBits (A i j) ≤ matrixEncodingLength A :=
  (Finset.single_le_sum (f := fun j => RAM.ratBits (A i j)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j)).trans
  (Finset.single_le_sum (f := fun i => ∑ j, RAM.ratBits (A i j)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i))

/-- The matrix bit count is precisely the contribution of the scalar matrix tape to the
public LP input layout. -/
theorem totalBits_lpInput {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    RAM.totalBits (lpInput A b) = matrixEncodingLength A + ∑ i, RAM.ratBits (b i) := by
  simp [RAM.totalBits, lpInput, matrixEncodingLength, List.map_flatten, List.map_ofFn,
    List.sum_flatten, List.sum_ofFn, Function.comp_def]

/-- For every square minor, a fixed quartic in the length of the original matrix suffices. -/
theorem rational_minor_bits {m d k : ℕ} (A : Matrix (Fin m) (Fin d) ℚ)
    (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin d) :
    let L := matrixEncodingLength A
    RAM.ratBits (A.submatrix rows cols).det ≤ 3 + 2*L^2 + 2*L^4 := by
  classical
  let L := matrixEncodingLength A
  have hk : k ≤ L := by
    obtain rfl | hk := eq_or_ne k 0
    · exact Nat.zero_le _
    let c := cols ⟨0, Nat.pos_of_ne_zero hk⟩
    have hrow (i : Fin m) : 1 ≤ ∑ j, RAM.ratBits (A i j) :=
      (show 1 ≤ RAM.ratBits (A i c) by unfold RAM.ratBits; omega).trans
        (Finset.single_le_sum (f := fun j => RAM.ratBits (A i j)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ c))
    calc
      k ≤ m := by simpa using Fintype.card_le_of_injective rows rows.injective
      _ = ∑ _ : Fin m, 1 := by simp
      _ ≤ L := Finset.sum_le_sum fun i _ => hrow i
  calc
    _ ≤ 3 + k^2 + L*k + 2*L*k^3 := rational_det_bits _ (fun i j => matrix_entry_bits_le A (rows i) (cols j))
    _ ≤ 3 + L^2 + L*L + 2*L*L^3 := by gcongr
    _ = 3 + 2*L^2 + 2*L^4 := by ring

/-- The public RAM input and its polynomial convention bound any signed minor. -/
theorem rational_minor_bits_lpInput {m d k : ℕ} (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin d) :
    RAM.ratBits (A.submatrix rows cols).det ≤ RAM.polyBound 7 4 (RAM.totalBits (lpInput A b)) := by
  let L := RAM.totalBits (lpInput A b)
  have hL : matrixEncodingLength A ≤ L := by
    change _ ≤ RAM.totalBits (lpInput A b)
    rw [totalBits_lpInput]; exact Nat.le_add_right ..
  calc
    _ ≤ 3 + 2 * (matrixEncodingLength A)^2 + 2 * (matrixEncodingLength A)^4 :=
      rational_minor_bits A rows cols
    _ ≤ 3 + 2 * L^2 + 2 * L^4 := by gcongr
    _ ≤ 7 * (L + 1)^4 := by ring_nf; omega

/-- The absolute logarithm of a nonzero scalar is bounded by its own binary length. -/
theorem abs_logb_rat_le_bits {q : ℚ} (hq : q ≠ 0) :
    abs (Real.logb 2 (abs (q : ℝ))) ≤ (RAM.ratBits q : ℝ) := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hnum : 0 < q.num.natAbs := Int.natAbs_pos.mpr (by simpa using hq)
  have hden := q.pos
  have log_bounds (z : ℕ) (hz : 0 < z) :
      0 ≤ Real.logb 2 (z : ℝ) ∧ Real.logb 2 (z : ℝ) ≤ (z.log2 : ℝ) + 1 := by
    refine ⟨Real.logb_nonneg hb (by exact_mod_cast hz), ?_⟩
    have h : (z : ℝ) ≤ (2 : ℝ) ^ (z.log2 + 1) := by exact_mod_cast Nat.lt_log2_self.le
    have hh := Real.logb_le_logb_of_le hb (by exact_mod_cast hz) h
    simpa [Real.logb_pow, Real.logb_self_eq_one hb] using hh
  have hn := log_bounds _ hnum
  have hd := log_bounds _ hden
  have habs : |(q : ℝ)| = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
    have hdabs : |(q.den : ℝ)| = (q.den : ℝ) := abs_of_nonneg (by positivity)
    rw [Rat.cast_def, abs_div, hdabs, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [habs, Real.logb_div (by positivity) (by positivity), abs_le]
  unfold RAM.ratBits
  push_cast
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) q.num.natAbs.log2,
    Nat.cast_nonneg (α := ℝ) q.den.log2]

/-- The mixed symbolic branch can charge its threshold to the original input length. -/
theorem rational_minor_abs_log {m d k : ℕ} (A : Matrix (Fin m) (Fin d) ℚ)
    (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin d) (hz : (A.submatrix rows cols).det ≠ 0) :
    let L := matrixEncodingLength A
    abs (Real.logb 2 (abs ((A.submatrix rows cols).det : ℝ))) ≤ ((3 + 2*L^2 + 2*L^4 : ℕ) : ℝ) :=
  (abs_logb_rat_le_bits hz).trans (Nat.cast_le.mpr (rational_minor_bits A rows cols))

end Compression
end LinearProgramming
end Optimization
end OAI
