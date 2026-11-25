import OAI.LinearAlgebra.FiniteFourier.PrimeFixedWidth

/-! # A fixed repair pencil over a finite free coefficient extension

The common clock width and the pencil coefficients are chosen before the
number of columns of a Fourier row. The check table may depend on the
frequency tuple in each particular row length.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Matrix MvPolynomial

variable {K : Type*} [CommRing K] [Nontrivial K] {ℓ m b : ℕ} [NeZero ℓ] [NeZero b] {ζ : K}

/-- Fixed coefficients and a certificate for one ordinary clock stage. -/
structure PrimeRepairPencil (ℓ m b : ℕ) [NeZero ℓ] (hζ : IsPrimitiveRoot ζ ℓ) where
  L : (Fin m → ZMod ℓ) → Matrix (Fin (primeClockDigits ℓ m b) → Fin b)
    (Fin (primeClockDigits ℓ m b) → Fin b) (MvPolynomial (Fin m × ZMod ℓ) K)
  A₀ : (Fin m → ZMod ℓ) → Matrix (Fin (primeClockDigits ℓ m b) → Fin b)
    (Fin (primeClockDigits ℓ m b) → Fin b) K
  A : (Fin m → ZMod ℓ) → Fin m → ZMod ℓ → Matrix (Fin (primeClockDigits ℓ m b) → Fin b)
    (Fin (primeClockDigits ℓ m b) → Fin b) K
  stage : ∀ β k, (L β).map (eval (queryPowerValues hζ k)) = A₀ β + ∑ j,
    ∑ a ∈ Finset.univ.erase (0 : ZMod ℓ), queryPowerValues hζ k (j,a) • A β j a
  power : ∀ β, (L β)^b = countPredictor hζ β (repairWindowLower ℓ m) (repairWindowDegree ℓ m) • 1

/-- The predictor pencil exists in any nontrivial coefficient ring carrying the
clock root and unit differences of its powers. -/
theorem exists_primeRepairPencil (hζ : IsPrimitiveRoot ζ ℓ) {ξ : K}
    (hpow : ξ^b = 1) (hu : ∀ k, 0 < k → k < b → IsUnit (ξ^k-1))
    (hD : repairWindowDegree ℓ m ≤ b) : Nonempty (PrimeRepairPencil ℓ m b hζ) := by
  obtain ⟨L,hdeg,hL⟩ := exists_fixed_width_matrix_roots hpow hu
    (fun β => countPredictor hζ β (repairWindowLower ℓ m) (repairWindowDegree ℓ m))
    (fun β => (countPredictor_totalDegree hζ β _ _).trans hD)
  choose A₀ A hstage using fun β => exists_queryPencil_coefficients hζ (L β) (hdeg β)
  exact ⟨⟨L, A₀, A, hstage, hL⟩⟩

omit [Nontrivial K] [NeZero b] in
/-- The fixed-width ordinary pencil and a spectral table recover the target on
every independent input row over the coefficient ring. -/
theorem PrimeRepairPencil.correct {hζ : IsPrimitiveRoot ζ ℓ} [PrimeSpectrumOrthogonal hζ]
    (p : PrimeRepairPencil ℓ m b hζ) (hℓ : 2 ≤ ℓ) (hm : 2 ≤ m) (u : K) (hu : u * (ℓ : K) = 1)
    (ρ : Fin (primePredictorRows ℓ m b) → K) (hρ : Pairwise fun i j => IsUnit (ρ i - ρ j))
    {V ν : Type*} [AddCommGroup V] [Module K V] (S : V ≃ₗ[K] (ν → K)) (k : ν → Fin m → ZMod ℓ)
    (Q : Fin m → Module.End K V)
    (hQ : ∀ j x ω, S (Q j x) ω = digitPhase hζ (k ω j) * S x ω) :
    let s := countRepairChecks ℓ m (b ^ primeClockDigits ℓ m b)
    ∃ T : ν → ((Fin s → K) × (Fin s → K)) →ₗ[K] ((Fin s → K) × (Fin s → K)),
      ∀ x i, hermiteRepairProgram ℓ u (queryPencilStage Q p.A₀ p.A)^[b]
        S (repairCheck ρ s) T x i = S.symm ((fun ω => countQueryProduct hζ (k ω)) * S (x i)) := by
  rw [queryPencilStage_eq_countPencilStep Q p.A₀ p.A hζ S k hQ p.L p.stage]
  apply exists_correct_hermiteRepairProgram S ρ hρ hu _ (fun ω => countQueryProduct_pow hζ (k ω))
    (fun ω => countPredictorEigenvalue hζ (k ω)) _
    (countPencilStep_iterate_predictor hζ S k p.L p.power)
    (fun ω => exceptionalShiftRowIndices (k ω) (b ^ primeClockDigits ℓ m b))
    (fun ω => exceptionalShiftRowIndices_card_le hℓ hm (k ω) _)
  intro ω i hi
  have hw := not_not.mp ((mem_exceptionalShiftRowIndices _ _).not.mp hi)
  exact eval_countPredictor_of_orthogonal hζ (isUnit_iff_exists_inv'.mpr ⟨u, hu⟩)
    _ _ hw.1 (by simpa only [repairWindowLower_add_degree] using hw.2)

end

end

end FiniteFourier
end LinearAlgebra
end OAI
