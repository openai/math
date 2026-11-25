import OAI.Computability.VPVNP.CNFNormalization
import OAI.Computability.VPVNP.ExactOnePadding
import OAI.Computability.VPVNP.HCWeighted
import OAI.Computability.VPVNP.PermanentWeighted
import OAI.Computability.VPVNP.CompleteFieldDescent
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Uniform projections from an integer weighted CNF

The graph sizes in §12 depend only on the clauses. We construct the Hamiltonian
projection over the integers and the permanent projection over the localization
of the integers at two. Changing the coefficient ring then preserves the same
source sizes and the same choices of variable labels.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open VPVNP VPVNP.HardnessCNF MvPolynomial

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] {k : ℕ}

/-- Keep the variable labels of a projection and apply a ring homomorphism to its scalars. -/
def castProjection (f : R →+* S) (w : Projection R σ τ) : Projection S σ τ :=
  fun i => (w i).map id f

private theorem map_label (f : R →+* S) (w : Projection R σ τ) (i : σ) :
    map f ((w i).elim X C) = (castProjection f w i).elim X C := by
  cases h : w i <;> simp [castProjection, h]

/-- Changing coefficients commutes with a literal variable-or-scalar substitution. -/
theorem map_projection_hom (f : R →+* S) (w : Projection R σ τ) (p : MvPolynomial σ R) :
    map f (w.hom p) = (castProjection f w).hom (map f p) := by
  have e : (map f).comp w.hom = (castProjection f w).hom.comp (map f) := by
    apply ringHom_ext
    · intro a
      simp [Projection.hom]
    · intro i
      simpa only [RingHom.comp_apply, Projection.hom, eval₂Hom_X', map_X] using map_label f w i
  exact DFunLike.congr_fun e p

/-- The integer identity for a weighted formula specializes at each scalar assignment. -/
theorem map_weightedCNF (f : R →+* S) (φ : CNF k) (w : Projection R (Fin k) τ) :
    map f (weightedCNF φ (fun i => (w i).elim X C)) =
      weightedCNF φ (fun i => (castProjection f w i).elim X C) := by
  classical
  simp only [weightedCNF, map_sum, apply_ite, map_zero, map_prod, map_one, map_label]

/-- The only coefficient inversion used by the permanent graph is that of two. -/
abbrev DyadicIntegers := Localization.Away (2 : ℤ)

private theorem dyadic_projection (φ : CNF k) (w : Projection DyadicIntegers (Fin k) τ) :
    let m := literalCount φ
    let r := 3 * m + k * (m + 2) + φ.length
    ∃ ψ : Projection DyadicIntegers (Fin r × Fin r) τ,
      ψ.hom (permanentPolynomial DyadicIntegers r) = ExactOne.weightedExactOne φ
        (fun i => (w i).elim X C) := by
  let b : DyadicIntegers := -IsLocalization.Away.invSelf (2 : ℤ)
  have hb : -2 * b = 1 := by
    calc
      -2 * b = algebraMap ℤ DyadicIntegers 2 * IsLocalization.Away.invSelf (2 : ℤ) := by
        simp only [map_ofNat, b]
        ring
      _ = 1 := IsLocalization.Away.mul_invSelf _
  have hbc : -2 * C (σ := τ) b = 1 := by
    simpa only [map_neg, map_ofNat, map_mul, map_one] using congrArg (C (σ := τ)) hb
  obtain ⟨ψ, hψ⟩ := PermanentReduction.weightedLabelsProjection (ExactOne.occurrences φ) w b
  exact ⟨ψ, hψ.trans (PermanentReduction.permanent_graph_eq_weighted φ _ _ hbc)⟩

/-- A family of integer-labelled CNFs has polynomial-size projections from the two
generic graph polynomials over their universal coefficient rings. The sizes are at
least two, as required by the Hamiltonian-cycle padding construction. -/
theorem integral_graph_projections {V : ℕ → Type*} {K : ℕ → ℕ}
    (φ : ∀ n, CNF (K n)) (w : ∀ n, Projection ℤ (Fin (K n)) (V n))
    (hk : PolynomiallyBounded K) (hl : PolynomiallyBounded fun n => literalCount (φ n)) :
    ∃ rH rP : ℕ → ℕ, PolynomiallyBounded rH ∧ PolynomiallyBounded rP ∧
      ∀ n, 2 ≤ rH n ∧ 2 ≤ rP n ∧
        (∃ ψ : Projection ℤ (Fin (rH n) × Fin (rH n)) (V n),
          ψ.hom (hamiltonianCyclePolynomial ℤ (rH n)) =
            weightedCNF (φ n) (fun i => (w n i).elim X C)) ∧
        ∃ ψ : Projection DyadicIntegers (Fin (rP n) × Fin (rP n)) (V n),
          ψ.hom (permanentPolynomial DyadicIntegers (rP n)) =
            map (Int.castRingHom DyadicIntegers) (weightedCNF (φ n) (fun i => (w n i).elim X C)) := by
  let ρ (n : ℕ) : CNF (K n) := normalizeClauses (φ n)
  let κ (n : ℕ) : ℕ := ExactOne.width (ρ n) + 1
  let δ (n : ℕ) : CNF (κ n) := ExactOne.pad (ExactOne.augment (ρ n))
  let m (n : ℕ) : ℕ := literalCount (δ n)
  let c (n : ℕ) : ℕ := (δ n).length
  have he {A : Type} [CommRing A] (n : ℕ) (v : Projection A (Fin (K n)) (V n)) :
      ExactOne.weightedExactOne (δ n) (fun i =>
        (ExactOne.padProjection (ExactOne.augmentProjection (ρ n) v) i).elim X C) =
        weightedCNF (φ n) (fun i => (v i).elim X C) := by
    dsimp only [δ, κ]
    rw [ExactOne.weightedExactOne_padProjection]
    simp_rw [ExactOne.augmentProjection_eval, ExactOne.weightedExactOne_augment, ρ,
      weightedCNF_normalizeClauses]
  obtain ⟨hL, hlen⟩ := normalizeClauses_polynomial_bounds φ hl
  obtain ⟨hwidth, hocc⟩ := ExactOne.polynomial_bounds ρ hk hL
  have hκ : PolynomiallyBounded κ := hwidth.add (.const 1)
  have hm : PolynomiallyBounded m := by
    simpa only [m, δ, ExactOne.literalCount_pad] using hocc.add (.const 1)
  have hc : PolynomiallyBounded c := by
    have hrows := (hlen.add (hL.pow 2)).of_le (fun n => ExactOne.length_augment_le (ρ n))
    simpa only [c, δ, ExactOne.length_pad] using hrows.add (.const 1)
  refine ⟨fun n => κ n * (3 * m n + 4) + c n, fun n => 3 * m n + κ n * (m n + 2) + c n,
    (hκ.mul (((PolynomiallyBounded.const 3).mul hm).add (.const 4))).add hc,
    (((PolynomiallyBounded.const 3).mul hm).add (hκ.mul (hm.add (.const 2)))).add hc, ?_⟩
  intro n
  have hκ₀ : 0 < κ n := Nat.succ_pos _
  have hH : 2 ≤ κ n * (3 * m n + 4) := by
    exact (show 2 ≤ 1 * (3 * m n + 4) by omega).trans (Nat.mul_le_mul_right _ hκ₀)
  have hP : 2 ≤ κ n * (m n + 2) := by
    exact (show 2 ≤ 1 * (m n + 2) by omega).trans (Nat.mul_le_mul_right _ hκ₀)
  refine ⟨by dsimp only; omega, by dsimp only; omega, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := HCGadget.weighted_projection (δ n) hκ₀
      (ExactOne.padProjection (ExactOne.augmentProjection (ρ n) (w n)))
    refine ⟨ψ, ?_⟩
    rw [← he (A := ℤ) n (w n)]
    exact hψ
  · let f := Int.castRingHom DyadicIntegers
    obtain ⟨ψ, hψ⟩ := dyadic_projection (δ n)
      (ExactOne.padProjection (ExactOne.augmentProjection (ρ n) (castProjection f (w n))))
    refine ⟨ψ, ?_⟩
    rw [map_weightedCNF f, ← he (A := DyadicIntegers) n (castProjection f (w n))]
    exact hψ

/-- Specialization of the dyadic scalar labels to any field whose characteristic differs
from two, including characteristic zero. -/
noncomputable def dyadicToField (F : Type*) [Field F] (q : ℕ) [CharP F q] (hq : q ≠ 2) :
    DyadicIntegers →+* F :=
  IsLocalization.Away.lift (2 : ℤ) (g := Int.castRingHom F)
    (by simpa using (Ring.two_ne_zero (by simpa [ringChar.eq F q] using hq) : (2 : F) ≠ 0).isUnit)

end BorderVNP
end Computability
end OAI
