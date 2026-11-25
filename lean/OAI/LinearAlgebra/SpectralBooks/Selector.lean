import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! # Integral wire widths and the selector cost

In the missing-flat argument, a rational wire multiplicity is scaled to an
integral number of bits. A further tensor power pays for the choice among
`K * L^j` networks using the strict saving in total length.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- Scale every positive rational wire multiplicity to a positive bit width. -/
theorem exists_common_wire_width {E : Type*} [Fintype E] (w : E → ℚ) (hw : ∀ e, 0 < w e) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : E → ℕ, ∀ e, 0 < b e ∧ (b e : ℚ) = m * w e := by
  classical
  let d (e : E) := (w e).den
  let rest (e : E) := ∏ i ∈ Finset.univ.erase e, d i
  refine ⟨∏ i, d i, Finset.prod_pos (fun i _ => (w i).den_pos), fun e =>
    rest e * (w e).num.toNat, ?_⟩
  intro e
  have hn := Rat.num_pos.mpr (hw e)
  have hnum : ((w e).num.toNat : ℚ) = (w e).num := by
    exact_mod_cast Int.toNat_of_nonneg hn.le
  have hd : rest e * d e = ∏ i, d i := Finset.prod_erase_mul _ _ (Finset.mem_univ e)
  refine ⟨Nat.mul_pos (Finset.prod_pos fun i _ => (w i).den_pos) (by omega), ?_⟩
  rw [← hd, Nat.cast_mul, Nat.cast_mul, hnum, mul_assoc]
  congr 1
  exact (Rat.den_mul_eq_num (w e)).symm

private theorem exists_nat_mul_gt (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ n : ℕ, 0 < n ∧ a < c * n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (a / c) 0)
  have hpos : (0 : ℝ) < n := (le_max_right _ _).trans_lt hn
  have hlt := (div_lt_iff₀ hc).mp ((le_max_left _ _).trans_lt hn)
  exact ⟨n, by exact_mod_cast hpos, by simpa [mul_comm] using hlt⟩

/-- Once the bit width pays for the exponential factor `L^j`, some positive
power pays for the remaining constant `K` in the number of summands. -/
theorem exists_selector_power {D m K L : ℕ} {γ : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hm : 2 * (D : ℝ) * Real.logb 2 L < γ * m) :
    ∃ j : ℕ, 0 < j ∧
      (2 * (D : ℝ) - γ) * m * j + 2 * D * Real.logb 2 ((K * L ^ j : ℕ) : ℝ) <
        2 * D * m * j := by
  obtain ⟨j, hj, hpower⟩ := exists_nat_mul_gt (2 * (D : ℝ) * Real.logb 2 K) (sub_pos.mpr hm)
  refine ⟨j, hj, ?_⟩
  have hKn : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hLn : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [Nat.cast_mul, Nat.cast_pow, Real.logb_mul hKn (pow_ne_zero _ hLn), Real.logb_pow]
  linarith only [hpower]

/-- The Euclidean cost of a scaled wire is bounded by its scaled length budget. -/
theorem scaled_wire_cost_le {w : ℚ} {b m : ℕ} {ℓ B : ℝ}
    (hb : (b : ℚ) = m * w) (hℓ : (w : ℝ) * ℓ ≤ B) : (b : ℝ) * ℓ ≤ B * m := by
  have h : (b : ℝ) = m * (w : ℝ) := by exact_mod_cast hb
  rw [h, mul_assoc, mul_comm B]
  exact mul_le_mul_of_nonneg_left hℓ (Nat.cast_nonneg _)

/-- A product of `j` wires has cost at most the sum of their common budgets. -/
theorem product_wire_cost_le {E : Type*} {b : E → ℕ} {ℓ : E → ℝ} {B : ℝ}
    (hwire : ∀ e, (b e : ℝ) * ℓ e ≤ B) {j : ℕ} (edges : Fin j → E) :
    ∑ i, (b (edges i) : ℝ) * ℓ (edges i) ≤ B * j := by
  calc
    _ ≤ ∑ _i : Fin j, B := Finset.sum_le_sum fun i _ ↦ hwire (edges i)
    _ = B * j := by simp [mul_comm]

/-- Choose the common wire scale before learning the prefactor `K` from
strict spectral comparison, as required by the shortening criterion. -/
theorem exists_selector_format {E : Type*} [Fintype E] (w : E → ℚ) (hw : ∀ e, 0 < w e)
    {D L : ℕ} (hL : 0 < L) {γ : ℝ} (hγ : 0 < γ) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : E → ℕ,
      (∀ e, 0 < b e ∧ (b e : ℚ) = m * w e) ∧
      2 * (D : ℝ) * Real.logb 2 L < γ * m ∧
      ∀ K : ℕ, 0 < K → ∃ j : ℕ, 0 < j ∧
        (2 * (D : ℝ) - γ) * m * j + 2 * D * Real.logb 2 ((K * L ^ j : ℕ) : ℝ) <
          2 * D * m * j := by
  obtain ⟨q, hq, bits, hbits⟩ := exists_common_wire_width w hw
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨n, hn, hbudget⟩ := exists_nat_mul_gt (2 * (D : ℝ) * Real.logb 2 L) (mul_pos hγ hq')
  have hm : 2 * (D : ℝ) * Real.logb 2 L < γ * ((n * q : ℕ) : ℝ) := by
    simpa [Nat.cast_mul, mul_left_comm, mul_comm, mul_assoc] using hbudget
  refine ⟨n * q, Nat.mul_pos hn hq, fun e ↦ n * bits e, ?_, hm, ?_⟩
  · intro e
    refine ⟨Nat.mul_pos hn (hbits e).1, ?_⟩
    simp only [Nat.cast_mul, (hbits e).2, mul_assoc]
  · exact fun _ hK ↦ exists_selector_power hK hL hm

end SpectralBooks
end LinearAlgebra
end OAI
