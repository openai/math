import OAI.LinearAlgebra.FiniteFourier.PrimeWindowPencil
import OAI.LinearAlgebra.FiniteFourier.PrimeRepairProgram
import OAI.LinearAlgebra.FiniteFourier.PrimeWindowWidth

/-! # Spectral repair for the shifted-count predictors

The same number of independent rows is allocated to every shift. The concrete
exceptional sets are small enough for the fixed Vandermonde checks. One table
recovers the common product on every row at every frequency.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

variable {ℓ m B : ℕ} [NeZero ℓ]

section Ring
variable {R : Type*} [CommRing R] {ζ : R}

/-- The number of check rows sufficient for the uniformly repeated shift batch. -/
def countRepairChecks (ℓ m B : ℕ) : ℕ := (ℓ ^ m * B) / (2 * m ^ 3)

/-- The scalar produced by the count predictor on a numbered row. -/
def countPredictorEigenvalue (hζ : IsPrimitiveRoot ζ ℓ) (k : Fin m → ZMod ℓ)
    (i : Fin (ℓ ^ m * B)) : R :=
  MvPolynomial.eval (queryPowerValues hζ k)
    (countPredictor hζ ((shiftRowEquivFin ℓ m B).symm i).1
      (repairWindowLower ℓ m) (repairWindowDegree ℓ m))

/-- The multiplier of the product of all the queries at the indicated frequency. -/
def countQueryProduct (hζ : IsPrimitiveRoot ζ ℓ) (k : Fin m → ZMod ℓ) : R :=
  ∏ j, digitPhase hζ (k j)

theorem countQueryProduct_pow (hζ : IsPrimitiveRoot ζ ℓ) (k : Fin m → ZMod ℓ) :
    countQueryProduct hζ k ^ ℓ = 1 := by
  rw [countQueryProduct, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro j _
  rw [digitPhase_apply, ← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

end Ring

variable {K V ν : Type*} [Field K] [AddCommGroup V] [Module K V] {ζ : K}

theorem countPredictorEigenvalue_eq_of_notMem (hζ : IsPrimitiveRoot ζ ℓ)
    (k : Fin m → ZMod ℓ) {i : Fin (ℓ ^ m * B)} (hi : i ∉ exceptionalShiftRowIndices k B) :
    countPredictorEigenvalue hζ k i = countQueryProduct hζ k := by
  apply eval_countPredictor_of_notMem_exceptionalShifts
  simpa [exceptionalShifts] using hi

omit [NeZero ℓ] in
/-- The integer interpolation window has the claimed square-root degree bound. -/
theorem repairWindowDegree_le_sqrt_mul_log (hℓ : 2 ≤ ℓ) (hm : 2 ≤ m) :
    (repairWindowDegree ℓ m : ℝ) ≤
      8 * ((ℓ : ℝ) - 1) * Real.sqrt ((m : ℝ) * Real.log (2 * m)) + 1 := by
  have h : (repairWindowDegree ℓ m : ℝ) ≤ 2 * (repairWindowRadius ℓ m : ℝ) + 1 := by
    exact_mod_cast repairWindowDegree_le ℓ m
  linarith only [h, repairWindowRadius_le_sqrt_mul_log hℓ hm]

/-- The source chooses the least power of the radix at least `max 2 D`. -/
def countPencilOrder (ℓ m : ℕ) : ℕ :=
  ℓ ^ Nat.clog ℓ (max 2 (repairWindowDegree ℓ m))

omit [NeZero ℓ] in
theorem countPencilOrder_bounds (hℓ : 2 ≤ ℓ) (m : ℕ) :
    max 2 (repairWindowDegree ℓ m) ≤ countPencilOrder ℓ m ∧
      countPencilOrder ℓ m < ℓ * max 2 (repairWindowDegree ℓ m) := by
  let M := max 2 (repairWindowDegree ℓ m)
  have hM : 1 < M := lt_of_lt_of_le (by decide : 1 < 2) (le_max_left ..)
  have ht := Nat.clog_pos hℓ hM
  refine ⟨Nat.le_pow_clog hℓ _, ?_⟩
  change ℓ ^ Nat.clog ℓ M < ℓ * M
  rw [← Nat.succ_pred_eq_of_pos ht, pow_succ']
  exact Nat.mul_lt_mul_of_pos_left (Nat.pow_pred_clog_lt_self hℓ hM) (by omega)

omit [NeZero ℓ] in
/-- Explicit stage budget for the `ℓ+2` predictor applications in a repaired batch. -/
theorem countRepair_stages_le (hℓ : 2 ≤ ℓ) (hm : 2 ≤ m) :
    ((ℓ : ℝ) + 2) * countPencilOrder ℓ m ≤ ((ℓ : ℝ) + 2) * ℓ *
      (8 * ((ℓ : ℝ) - 1) * Real.sqrt ((m : ℝ) * Real.log (2 * m)) + 2) := by
  have h : (countPencilOrder ℓ m : ℝ) ≤ (ℓ : ℝ) * max 2 (repairWindowDegree ℓ m : ℝ) := by
    exact_mod_cast (countPencilOrder_bounds hℓ m).2.le
  have hd := repairWindowDegree_le_sqrt_mul_log hℓ hm
  have hnonneg : 0 ≤ 8 * ((ℓ : ℝ) - 1) *
      Real.sqrt ((m : ℝ) * Real.log (2 * m)) :=
    mul_nonneg (mul_nonneg (by norm_num) (by exact_mod_cast (by omega : 0 ≤ (ℓ : ℤ) - 1)))
      (Real.sqrt_nonneg _)
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact h.trans (mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) (Nat.cast_nonneg ℓ))

/-- A program applying the concrete count predictors is repaired on every input
by a single table on two blocks of `countRepairChecks ℓ m B` rows. The frequency
patterns, check nodes, spectral equivalence and ordinary predictor are supplied
by the calling circuit construction. -/
theorem exists_correct_countRepair_of_action (hℓ : 2 ≤ ℓ) (hm : 2 ≤ m)
    (hζ : IsPrimitiveRoot ζ ℓ) (S : V ≃ₗ[K] (ν → K)) (k : ν → Fin m → ZMod ℓ)
    (ρ : Fin (ℓ ^ m * B) → K) (hρ : Function.Injective ρ)
    (P : (Fin (ℓ ^ m * B) → V) → (Fin (ℓ ^ m * B) → V))
    (hP : ∀ x i ω, S (P x i) ω = countPredictorEigenvalue hζ (k ω) i * S (x i) ω) :
    let s := countRepairChecks ℓ m B
    ∃ T : ν → ((Fin s → K) × (Fin s → K)) →ₗ[K] ((Fin s → K) × (Fin s → K)),
      ∀ x i, hermiteRepairProgram ℓ (ℓ : K)⁻¹ P S (repairCheck ρ s) T x i =
        S.symm ((fun ω => countQueryProduct hζ (k ω)) * S (x i)) := by
  apply exists_correct_hermiteRepairProgram S ρ
    (fun _ _ hij => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hρ.ne hij)))
    (inv_mul_cancel₀ hζ.neZero'.out) _ (fun ω => countQueryProduct_pow hζ (k ω))
    (fun ω => countPredictorEigenvalue hζ (k ω)) P hP (fun ω => exceptionalShiftRowIndices (k ω) B)
    (fun ω => exceptionalShiftRowIndices_card_le hℓ hm (k ω) B)
  intro ω i hi
  exact countPredictorEigenvalue_eq_of_notMem hζ _ hi

/-- A common-width affine pencil and a single Hermite table repair the product
on all independent copies of all shifts. The selected row indices use at most
the fraction `1/(2m³)` of the batch at each frequency. -/
theorem exists_correct_countPencilRepair {b : ℕ} [NeZero b] {ξ : K}
    (hℓ : 2 ≤ ℓ) (hm : 2 ≤ m) (hζ : IsPrimitiveRoot ζ ℓ) (hξ : IsPrimitiveRoot ξ b)
    (hD : repairWindowDegree ℓ m ≤ b) (S : V ≃ₗ[K] (ν → K)) (k : ν → Fin m → ZMod ℓ) :
    ∃ (h : ℕ) (L : (Fin m → ZMod ℓ) →
        Matrix (Fin h → Fin b) (Fin h → Fin b) (MvPolynomial (Fin m × ZMod ℓ) K)),
      (∀ β i j, ((L β) i j).totalDegree ≤ 1) ∧
      (∀ β, (L β) ^ b = countPredictor hζ β (repairWindowLower ℓ m) (repairWindowDegree ℓ m) • 1) ∧
      ∀ (ρ : Fin (ℓ ^ m * b ^ h) → K), Function.Injective ρ →
        let s := countRepairChecks ℓ m (b ^ h)
        ∃ T : ν → ((Fin s → K) × (Fin s → K)) →ₗ[K] ((Fin s → K) × (Fin s → K)),
          ∀ x i, hermiteRepairProgram ℓ (ℓ : K)⁻¹ (countPencilStep hζ S k L)^[b]
            S (repairCheck ρ s) T x i = S.symm ((fun ω => countQueryProduct hζ (k ω)) * S (x i)) := by
  obtain ⟨h, L, haff, hL, _⟩ := exists_countPredictor_pencils hζ hξ (repairWindowLower ℓ m) hD
  refine ⟨h, L, haff, hL, fun ρ hρ => ?_⟩
  apply exists_correct_countRepair_of_action hℓ hm hζ S k ρ hρ _
  exact countPencilStep_iterate_predictor hζ S k L hL

end

end

end FiniteFourier
end LinearAlgebra
end OAI
