import OAI.LinearAlgebra.FiniteFourier.PrimeMonomialFactors
import OAI.LinearAlgebra.FiniteFourier.PrimeClockShift
import OAI.LinearAlgebra.FiniteFourier.PrimePredictor

/-! # Matrix evaluation of a bounded-degree polynomial

The construction uses common-width blocks for a finite family of polynomials.
A block width is `b^h`, including width one when the family has no monomials.
Every block row is an independent input.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open MvPolynomial Matrix
noncomputable section

/-- The matrix-root lemma for a finite family over an integral domain
containing a primitive `b`-th root. The matrices have affine-linear entries
and a common nonempty row type. -/
theorem exists_common_affine_matrix_roots {K σ B : Type*} [CommRing K] [IsDomain K] [Fintype B]
    {b : ℕ} [NeZero b] {ξ : K} (hξ : IsPrimitiveRoot ξ b) (p : B → MvPolynomial σ K)
    (hp : ∀ v, (p v).totalDegree ≤ b) :
    ∃ (h : ℕ) (L : B → Matrix (Fin h → Fin b) (Fin h → Fin b) (MvPolynomial σ K)),
      (∀ v x y, ((L v) x y).totalDegree ≤ 1) ∧ ∀ v, (L v) ^ b = p v • 1 := by
  classical
  obtain ⟨h, f, hf, hp'⟩ := family_eq_sum_prod_affine p (NeZero.pos b) hp
  refine ⟨h, fun v => ∑ i, qClockTerm (C ξ) (f v) i, ?_, ?_⟩
  · intro v x y
    dsimp only
    rw [Matrix.sum_apply x y _ (fun i => qClockTerm (C ξ) (f v) i)]
    exact totalDegree_finsetSum_le fun i _ => qClockTerm_affine ξ (f v) (hf v) i x y
  · intro v
    have hq : IsPrimitiveRoot (C ξ : MvPolynomial σ K) b :=
      hξ.map_of_injective (MvPolynomial.C_injective σ K)
    rw [qClock_sum_pow hq (f v), ← hp' v]

/-- The polynomial matrix identity remains valid under arbitrary specialization.
The target ring may have zero divisors. -/
theorem specialize_matrix_root {A R I : Type*} [CommRing A] [CommRing R] [Fintype I] [DecidableEq I]
    (g : A →+* R) {L : Matrix I I A} {p : A} {b : ℕ} (hL : L ^ b = p • 1) :
    (L.map g) ^ b = g p • 1 := by
  rw [← Matrix.map_pow, hL]
  ext i j
  by_cases hij : i = j <;> simp [hij]

/-- Each shift's count predictor has a common-width `b`-stage pencil.
At frequencies in its window the resulting power multiplies every input by
the product of the query eigenvalues. -/
theorem exists_countPredictor_pencils {K : Type*} [Field K] {ℓ b m D : ℕ} [NeZero ℓ] [NeZero b]
    {ζ ξ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hξ : IsPrimitiveRoot ξ b) (u : ℤ) (hD : D ≤ b) :
    ∃ (h : ℕ) (L : (Fin m → ZMod ℓ) →
      Matrix (Fin h → Fin b) (Fin h → Fin b) (MvPolynomial (Fin m × ZMod ℓ) K)),
      (∀ β x y, ((L β) x y).totalDegree ≤ 1) ∧
      (∀ β, (L β) ^ b = countPredictor hζ β u D • 1) ∧
      ∀ β k, u ≤ shiftedCount k β → (shiftedCount k β : ℤ) ≤ u + D →
        ((L β).map (eval (queryPowerValues hζ k))) ^ b = (∏ j, digitPhase hζ (k j)) • 1 := by
  obtain ⟨h, L, haff, hL⟩ := exists_common_affine_matrix_roots hξ
    (fun β : Fin m → ZMod ℓ => countPredictor hζ β u D)
    (fun β => (countPredictor_totalDegree hζ β u D).trans hD)
  refine ⟨h, L, haff, hL, ?_⟩
  intro β k hlo hhi
  rw [specialize_matrix_root _ (hL β), eval_countPredictor hζ k β hlo hhi]

end

end FiniteFourier
end LinearAlgebra
end OAI
