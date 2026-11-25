import OAI.LinearAlgebra.SpectralBooks.BooleanChoice.SignedBooleanGraphHardness

/-! # One integral independent-set graph family in every characteristic

The graph and the variable-or-integer substitutions can be chosen over the
integers. Scalar extension preserves those substitutions and the graph itself.
Thus the order and the adjacency relation are independent of the ground field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
namespace IndependentSetGraph
open Filter
open scoped Classical
universe u

theorem map_project {R S σ τ : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (p : σ → ProjectionAtom R τ) (f : MvPolynomial σ R) :
    MvPolynomial.map φ (project p f) = project (fun i => (p i).map id φ) (MvPolynomial.map φ f) := by
  simp only [project, MvPolynomial.aeval_eq_bind₁, MvPolynomial.map_bind₁]
  congr 2
  funext i
  cases h : p i <;> simp [atomPolynomial]

theorem map_gridPolynomial {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m k : ℕ}
    (G : Fin m → Fin k → Prop) : MvPolynomial.map φ (IndependentSetGrid.polynomial G) =
      IndependentSetGrid.polynomial (R := S) G := by
  simp [IndependentSetGrid.polynomial, IndependentSetGrid.generatingSum, map_sum, apply_ite, map_prod]

/-- Scalar extension specializes the same graph and the same pins. -/
def GridProjection.map {R S σ : Type*} [CommRing R] [CommRing S] {N : ℕ} {f : MvPolynomial σ R}
    (G : GridProjection R σ f N) (φ : R →+* S) : GridProjection S σ (MvPolynomial.map φ f) N where
  m := G.m
  k := G.k
  size_eq := G.size_eq
  edge := G.edge
  row_degree := G.row_degree
  col_degree := G.col_degree
  pin i := (G.pin i).map id φ
  identity := by
    simpa only [map_project, map_gridPolynomial] using congrArg (MvPolynomial.map φ) G.identity

private def integralGrid {σ : Type*} {f : MvPolynomial σ ℤ} {N : ℕ}
    (G : GridProjection ℤ σ f N) : SubcubicGrid N :=
  ⟨G.m, G.k, G.size_eq, G.edge, G.row_degree, G.col_degree⟩

/-- The very same graphs serve every field and every source exponent. -/
theorem exists_gridFamily_of_integral_projections {σ : ℕ → Type*}
    (f : (n : ℕ) → MvPolynomial (σ n) ℤ) {A b : ℕ} (hA : 0 < A) (hb : 0 < b)
    (hproj : ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, A*n^b ≤ N → Nonempty (GridProjection ℤ (σ n) (f n) N)) :
    ∃ G : (N : ℕ) → SubcubicGrid N, ∀ (F : Type u) [Field F] {ε δ : ℝ}, 0 < ε → 0 < δ → δ < ε / b →
      (∀ᶠ n : ℕ in atTop, DegreeBorderSizeAtLeast n ((2:ℝ)^((n:ℝ)^ε))
        (MvPolynomial.map (Int.castRingHom F) (f n))) →
      ∀ᶠ N : ℕ in atTop, DegreeBorderSizeAtLeast N ((2:ℝ)^((N:ℝ)^δ))
        (IndependentSetGrid.polynomial (R := F) (G N).edge) := by
  classical
  have hAr : 0 < (A:ℝ) := by exact_mod_cast hA
  have hbr : 0 < (b:ℝ) := by exact_mod_cast hb
  let n := paddingIndex (A := (A:ℝ)) (b := (b:ℝ))
  let good (N : ℕ) := Nonempty (GridProjection ℤ (σ (n N)) (f (n N)) N)
  have hg : ∀ᶠ N : ℕ in atTop, good N := by
    filter_upwards [(paddingIndex_tendsto hAr hbr).eventually hproj] with N h
    apply h
    have bound := paddingIndex_bound hAr hbr N
    rw [Real.rpow_natCast] at bound
    exact_mod_cast bound
  let G (N : ℕ) : SubcubicGrid N := if h : good N then integralGrid h.some else
    ⟨N, 0, Nat.add_zero _, fun _ _ => False, by simp, by simp⟩
  refine ⟨G, ?_⟩
  intro F inst ε δ hε hδ hgap hlower
  let source (i : ℕ) := degreeBorderSize i (MvPolynomial.map (Int.castRingHom F) (f i))
  let target (N : ℕ) := degreeBorderSize N (IndependentSetGrid.polynomial (R := F) (G N).edge)
  apply borderSize_lower_of_indexed_padding (source := source) (target := target) hAr hbr
    (C := 2) (by norm_num) hε hδ hgap hlower
  filter_upwards [hg] with N h
  have bound := (h.some.map (Int.castRingHom F)).borderSize_le (n N)
  dsimp only [target, source, G]
  rw [dite_eq_left h]
  exact_mod_cast bound.trans (Nat.mul_le_mul_left _ (Nat.le_add_left _ 1))

/-- A polynomial-size signed Boolean verifier selects one graph per order
whose border lower bound transfers simultaneously to every characteristic. -/
theorem exists_gridFamily_of_signedVerifier (h : BooleanChoice.PolynomialSignedVerifier) :
    ∃ (b : ℕ) (G : (N : ℕ) → SubcubicGrid N), 0 < b ∧
      ∀ (F : Type u) [Field F] {ε δ : ℝ}, 0 < ε → 0 < δ → δ < ε / b → SignedWitnessHardness F ε →
        ∀ᶠ N : ℕ in atTop, DegreeBorderSizeAtLeast N ((2:ℝ)^((N:ℝ)^δ))
          (IndependentSetGrid.polynomial (R := F) (G N).edge) := by
  obtain ⟨A,b,hA,hb,hp⟩ := (BooleanChoice.choicePresentation_signedWitness (R := ℤ) h).gridProjections
  obtain ⟨G,hG⟩ := exists_gridFamily_of_integral_projections _ hA hb hp
  refine ⟨b,G,hb,?_⟩
  intro F inst ε δ hε hδ hgap hard
  apply hG F hε hδ hgap
  simpa only [map_signedWitnessPolynomial, SignedWitnessHardness] using hard

end IndependentSetGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
