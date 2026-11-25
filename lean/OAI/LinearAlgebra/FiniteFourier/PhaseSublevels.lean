import OAI.LinearAlgebra.FiniteFourier.PhasePrice
import OAI.LinearAlgebra.SpectralBooks.SpectralSublevels

/-! # Closed sublevels of the controlled-phase rectangle value

The four-leg lift is polynomial in matrix coordinates: each coefficient is
either zero or one matrix entry. The closed-sublevel theorem for a normalized
spectral point therefore applies in each fixed matrix format. The rectangle
value assigns zero to the zero matrix.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
open scoped Classical
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

section

variable {K : Type*} [Field K] {R C : Type} [Fintype R] [Fintype C]

/-- Matrices in affine coordinates indexed by a row-column pair. -/
abbrev matrixPoint (M : Matrix R C K) (q : R × C) : K := M q.1 q.2

/-- The phase lift carries matrix Zariski closure to tensor Zariski closure. -/
theorem phaseRaw_mem_closure {S : Set (Matrix R C K)} {M : Matrix R C K}
    (h : matrixPoint M ∈ affineZariskiClosure (matrixPoint '' S)) :
    (phaseRaw M).coeff ∈ affineZariskiClosure ((fun A : Matrix R C K => (phaseRaw A).coeff) '' S) := by
  let f (z : ∀ i, phaseLeg R C i) : MvPolynomial (R × C) K :=
    if (z 0 : R) = z 2 ∧ (z 1 : C) = z 3 then MvPolynomial.X (z 0, z 1) else 0
  have he (A : Matrix R C K) :
      (fun z => MvPolynomial.eval (matrixPoint A) (f z)) = (phaseRaw A).coeff := by
    funext z
    rw [phaseRaw_coeff]
    dsimp only [f, phaseEntry]
    split_ifs <;> simp [matrixPoint]
    all_goals
      rename_i h₁ h₂
      first | exact (h₁ h₂).elim | exact (h₂ h₁).elim
  rw [← he]
  apply mapsTo_affineZariskiClosure_of_polynomial f _ h
  rintro _ ⟨A, hA, rfl⟩
  exact ⟨A, hA, (he A).symm⟩

omit [Fintype R] [Fintype C] in
private theorem exists_member_of_mem_matrixClosure {S : Set (Matrix R C K)} {M : Matrix R C K}
    (h : matrixPoint M ∈ affineZariskiClosure (matrixPoint '' S)) : S.Nonempty := by
  by_contra! hn
  have hf := h (1 : MvPolynomial (R × C) K) (by simp [hn])
  simp at hf

omit [Fintype R] [Fintype C] in
private theorem exists_nonzero_of_mem_matrixClosure {S : Set (Matrix R C K)} {M : Matrix R C K}
    (h : matrixPoint M ∈ affineZariskiClosure (matrixPoint '' S)) (hne : M ≠ 0) :
    ∃ A ∈ S, A ≠ 0 := by
  by_contra! hz
  apply hne
  ext r c
  have hr := h (MvPolynomial.X (r, c)) (by
    rintro _ ⟨A, hA, rfl⟩
    simp [hz A hA, matrixPoint])
  simpa [matrixPoint] using hr

/-- The placed price bound persists on all nonzero matrices in the closure,
even when some of the four placement sites coincide. -/
theorem fourierPhasePrice_le_of_mem_closure (P : SpectralPlacementPrices K Plane)
    (x : Fin 4 → Plane) {S : Set (Matrix R C K)} {M : Matrix R C K}
    (h : matrixPoint M ∈ affineZariskiClosure (matrixPoint '' S)) (hne : M ≠ 0)
    {B : ℝ} (hb : ∀ A ∈ S, A ≠ 0 → fourierPhasePrice P A x ≤ B) :
    fourierPhasePrice P M x ≤ B := by
  rcases placed_price_normalized_or_collapsed P x with hc | ⟨φ, a, ha, he⟩
  · obtain ⟨A, hA, hAn⟩ := exists_nonzero_of_mem_matrixClosure h hne
    simpa [fourierPhasePrice, hc] using hb A hA hAn
  · change P.price (phaseRaw M) x ≤ B
    rw [he]
    apply logPrice_le_of_mem_closure φ (phaseRaw_mem_closure h) (phaseRaw_coeff_ne_zero.mpr hne) ha.le
    rintro _ ⟨A, hA, rfl⟩ hAn
    have hb' := hb A hA (phaseRaw_coeff_ne_zero.mp hAn)
    change P.price (phaseRaw A) x ≤ B at hb'
    rw [he] at hb'
    exact hb'

omit [Fintype R] [Fintype C] in
private theorem sublevel_polynomials {v : Matrix R C K → ℝ} {B : ℝ}
    (closed : ∀ M, matrixPoint M ∈ affineZariskiClosure (matrixPoint '' {A | v A ≤ B}) → v M ≤ B) :
    ∃ polys : Set (MvPolynomial (R × C) K), ∀ M,
      v M ≤ B ↔ ∀ p ∈ polys, MvPolynomial.eval (matrixPoint M) p = 0 := by
  let polys : Set (MvPolynomial (R × C) K) := {p | ∀ A, v A ≤ B → MvPolynomial.eval (matrixPoint A) p = 0}
  refine ⟨polys, fun M => ⟨fun h p hp => hp M h, ?_⟩⟩
  intro h
  apply closed
  intro p hp
  exact h p (fun A hA => hp _ ⟨A, hA, rfl⟩)

/-- Polynomial equations for the sublevel of the four-site phase price itself. -/
theorem fourierPhasePrice_sublevel_polynomials (P : SpectralPlacementPrices K Plane)
    (x : Fin 4 → Plane) (B : ℝ) :
    ∃ polys : Set (MvPolynomial (R × C) K), ∀ M : Matrix R C K,
      fourierPhasePrice P M x ≤ B ↔ ∀ p ∈ polys, MvPolynomial.eval (matrixPoint M) p = 0 := by
  apply sublevel_polynomials
  intro M hM
  by_cases hne : M = 0
  · obtain ⟨A, hA⟩ := exists_member_of_mem_matrixClosure hM
    change fourierPhasePrice P A x ≤ B at hA
    subst M
    change P.price (phaseRaw (0 : Matrix R C K)) x ≤ B
    have hz : (phaseRaw (0 : Matrix R C K)).coeff = 0 := not_ne_iff.mp fun hn =>
      phaseRaw_coeff_ne_zero.mp hn rfl
    rw [P.zero_tensor _ hz]
    have ha : 0 ≤ fourierPhasePrice P A x := by
      rcases placed_price_normalized_or_collapsed P x with hc | ⟨φ, a, ha, he⟩
      · simp [fourierPhasePrice, hc]
      · simpa only [fourierPhasePrice, he] using rawLogPrice_nonneg φ ha.le (phaseRaw A)
    exact ha.trans hA
  · exact fourierPhasePrice_le_of_mem_closure P x hM hne (fun _ h _ => h)

/-- Polynomial equations for the rectangle-value sublevel. The positive denominator
is the normalized rectangle diagonal price. -/
theorem rectangleValue_sublevel_polynomials (P : SpectralPlacementPrices K Plane) (s c B : ℝ)
    (hpos : 0 < c + s) :
    ∃ polys : Set (MvPolynomial (R × C) K), ∀ M : Matrix R C K,
      rectangleValue (fourierPhasePrice P) M s c ≤ B ↔
        ∀ p ∈ polys, MvPolynomial.eval (matrixPoint M) p = 0 := by
  apply sublevel_polynomials
  intro M hM
  let v (A : Matrix R C K) := rectangleValue (fourierPhasePrice P) A s c
  by_cases hn : M = 0
  · obtain ⟨A, hA⟩ := exists_member_of_mem_matrixClosure hM
    change v A ≤ B at hA
    have ha : 0 ≤ v A := by dsimp [v, rectangleValue]; split <;> positivity
    simpa [hn, rectangleValue] using ha.trans hA
  · obtain ⟨A, hA, hAn⟩ := exists_nonzero_of_mem_matrixClosure hM hn
    change v A ≤ B at hA
    have ha : 0 < v A := by dsimp [v, rectangleValue]; rw [ite_eq_right hAn]; positivity
    have hB := ha.trans_le hA
    let d := 2 * (c + s)
    have hd : 0 < d := mul_pos (by norm_num) hpos
    have eqv (N : Matrix R C K) (hN : N ≠ 0) : v N ≤ B ↔
        fourierPhasePrice P N (rectangleSites (2 * s) (2 * c)) ≤ Real.logb 2 B * d := by
      dsimp only [v, rectangleValue, rectanglePrice, d]
      rw [ite_eq_right hN, ← Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hB,
        div_le_iff₀ hd]
    apply (eqv M hn).mpr
    exact fourierPhasePrice_le_of_mem_closure P _ hM hn (fun N hN hnz => (eqv N hnz).mp hN)

end

end

end FiniteFourier
end LinearAlgebra
end OAI
