import OAI.LinearAlgebra.SpectralBooks.BorderCircuitProjection
import OAI.LinearAlgebra.SpectralBooks.ProjectionGrowth
import OAI.LinearAlgebra.SpectralBooks.SignedWitnessBorder
import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.ChoiceTable
import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.IndependentSetCompleteGraphs

/-! # Stretched-exponential hardness of subcubic bipartite independent-set grids

A polynomial-size projection at every larger order transfers a border-size
exponent to the corresponding homogeneous graph polynomials. The source order
for target order `N` is the integer part of the inverse polynomial growth law.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
section
open Filter
open scoped Classical

structure SubcubicGrid (N : ℕ) where
  m : ℕ
  k : ℕ
  order : m + k = N
  edge : Fin m → Fin k → Prop
  row_degree : ∀ i, Fintype.card {j // edge i j} ≤ 3
  col_degree : ∀ j, Fintype.card {i // edge i j} ≤ 3

/-- In each sufficiently large order the degree component of the graph polynomial
has the stated border-size lower bound. -/
def HardSubcubicGrids (F : Type*) [Field F] (δ : ℝ) : Prop :=
  ∃ G : (N : ℕ) → SubcubicGrid N, ∀ᶠ N : ℕ in atTop,
    DegreeBorderSizeAtLeast N ((2:ℝ)^((N:ℝ)^δ)) (IndependentSetGrid.polynomial (R := F) (G N).edge)

namespace IndependentSetGraph

theorem GridProjection.borderSize_le {F σ : Type*} [Field F] {N : ℕ} {f : MvPolynomial σ F}
    (G : GridProjection F σ f N) (d : ℕ) :
    degreeBorderSize d f ≤ 2*(N+1)^2*degreeBorderSize N (IndependentSetGrid.polynomial (R := F) G.edge) := by
  have hh := IndependentSetGrid.polynomial_isHomogeneous (R := F) G.edge
  rw [G.size_eq] at hh
  have h := degreeBorderSize_projection_le N d G.pin _ hh
  change degreeBorderSize d (IndependentSetGraph.project G.pin _) ≤ _ at h
  simpa only [G.identity] using h

private def GridProjection.grid {R σ : Type*} [CommRing R] {N : ℕ} {f : MvPolynomial σ R}
    (G : GridProjection R σ f N) : SubcubicGrid N :=
  ⟨G.m, G.k, G.size_eq, G.edge, G.row_degree, G.col_degree⟩

private def fallbackGrid (N : ℕ) : SubcubicGrid N :=
  ⟨N, 0, Nat.add_zero _, fun _ _ => False, by simp, by simp⟩

/-- Projecting a stretched-exponentially hard family from the grids at each
larger order gives the graph lower bound at all sufficiently large orders. -/
theorem hardSubcubicGrids_of_polynomial_projections {F : Type*} [Field F] {σ : ℕ → Type*}
    (f : (n : ℕ) → MvPolynomial (σ n) F) {A b : ℕ} (hA : 0 < A) (hb : 0 < b)
    (projected : ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, A*n^b ≤ N → Nonempty (GridProjection F (σ n) (f n) N))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hgap : δ < ε / b)
    (hlower : ∀ᶠ n : ℕ in atTop, DegreeBorderSizeAtLeast n ((2:ℝ)^((n:ℝ)^ε)) (f n)) :
    HardSubcubicGrids F δ := by
  classical
  have hAr : 0 < (A:ℝ) := by exact_mod_cast hA
  have hbr : 0 < (b:ℝ) := by exact_mod_cast hb
  let n := paddingIndex (A := (A:ℝ)) (b := (b:ℝ))
  let good (N : ℕ) := Nonempty (GridProjection F (σ (n N)) (f (n N)) N)
  have eventually_good : ∀ᶠ N : ℕ in atTop, good N := by
    filter_upwards [(paddingIndex_tendsto hAr hbr).eventually projected] with N hp
    apply hp
    have bound := paddingIndex_bound hAr hbr N
    rw [Real.rpow_natCast] at bound
    exact_mod_cast bound
  let G (N : ℕ) : SubcubicGrid N := if hp : good N then hp.some.grid else fallbackGrid N
  refine ⟨G, ?_⟩
  let source (i : ℕ) := degreeBorderSize i (f i)
  let target (N : ℕ) := degreeBorderSize N (IndependentSetGrid.polynomial (R := F) (G N).edge)
  apply borderSize_lower_of_indexed_padding (source := source) (target := target) hAr hbr
    (C := 2) (by norm_num) hε hδ hgap hlower
  filter_upwards [eventually_good] with N hp
  have hbnd := (hp.some.borderSize_le (n N))
  change (degreeBorderSize (n N) (f (n N)) : ℝ) ≤ 2 * ((N:ℝ)+1)^2 *
    (1+(degreeBorderSize N (IndependentSetGrid.polynomial (R := F) (G N).edge) : ℝ))
  dsimp only [G]
  rw [dite_eq_left hp]
  exact_mod_cast hbnd.trans (Nat.mul_le_mul_left _ (Nat.le_add_left _ 1))

/-- A table needs at most `51*u²` grid vertices when its block and option
counts sum to at most the positive budget `u`. -/
theorem ChoiceTable.gridProjection {R σ : Type*} [CommRing R] (t : ChoiceTable R σ) {u N : ℕ}
    (hu : 0 < u) (ht : t.size ≤ u) (hN : 51*u^2 ≤ N) : Nonempty (GridProjection R σ t.polynomial N) := by
  apply exists_gridProjection_of_choices t.conflict t.w
  let q := Fintype.card (Sigma t.Option)
  let d := Fintype.card t.Block
  change q + d + 25*(q^2+q) ≤ N
  change d + q ≤ u at ht
  have hq : q ≤ u := by omega
  have hs : q^2 ≤ u^2 := Nat.pow_le_pow_left hq 2
  have hu2 : u ≤ u^2 := by nlinarith
  omega

/-- Flattening the local verifier to a grid squares its size bound. -/
theorem HasPolynomialChoicePresentation.gridProjections {R : Type*} [CommRing R] {σ : ℕ → Type*}
    {f : (n : ℕ) → MvPolynomial (σ n) R} (hp : HasPolynomialChoicePresentation R f) :
    ∃ A k : ℕ, 0 < A ∧ 0 < k ∧ ∀ᶠ n : ℕ in atTop,
      ∀ N : ℕ, A*n^k ≤ N → Nonempty (GridProjection R (σ n) (f n) N) := by
  obtain ⟨C,b,hC,hb, hp⟩ := hp
  refine ⟨51*C^2, 2*b, by positivity, by positivity, ?_⟩
  filter_upwards [hp, eventually_ge_atTop 1] with n ht hn
  obtain ⟨t,htf,ht⟩ := ht
  intro N hN
  rw [← htf]
  apply t.gridProjection (u := C*n^b) (Nat.mul_pos hC (pow_pos (by omega) _)) ht
  convert hN using 1
  simp [mul_pow, ← pow_mul, Nat.mul_comm b 2, Nat.mul_assoc]

theorem hardSubcubicGrids_of_choicePresentation {F : Type*} [Field F] {σ : ℕ → Type*}
    (f : (n : ℕ) → MvPolynomial (σ n) F) (hp : HasPolynomialChoicePresentation F f)
    {ε : ℝ} (hε : 0 < ε)
    (hlower : ∀ᶠ n : ℕ in atTop, DegreeBorderSizeAtLeast n ((2:ℝ)^((n:ℝ)^ε)) (f n)) :
    ∃ δ : ℝ, 0 < δ ∧ HardSubcubicGrids F δ := by
  obtain ⟨A,k,hA,hk,hp⟩ := hp.gridProjections
  have hkr : 0 < (k:ℝ) := by exact_mod_cast hk
  have hpos : 0 < ε / k := div_pos hε hkr
  exact ⟨(ε / k) / 2, by positivity, hardSubcubicGrids_of_polynomial_projections f hA hk hp
    hε (by positivity) (by linarith) hlower⟩

/-- The independent-set part of the Tree corollary from a local verifier for
the signed universal polynomial and its degree-component lower bound. -/
theorem hardSubcubicGrids_of_signedWitness {F : Type*} [Field F]
    (hp : HasPolynomialChoicePresentation F (signedWitnessPolynomial F)) {ε : ℝ}
    (hε : 0 < ε) (hard : SignedWitnessHardness F ε) :
    ∃ δ : ℝ, 0 < δ ∧ HardSubcubicGrids F δ :=
  hardSubcubicGrids_of_choicePresentation _ hp hε hard

end IndependentSetGraph
end

end

end SpectralBooks
end LinearAlgebra
end OAI
