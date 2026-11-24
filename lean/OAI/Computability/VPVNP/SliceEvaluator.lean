import OAI.Computability.VPVNP.Evaluator
import OAI.Computability.VPVNP.FiniteSlice
import OAI.Computability.VPVNP.MonomialBasis
import Mathlib.FieldTheory.PrimitiveElement

/-!
# The path-counting evaluator on a finite geometric slice

For a nonempty finite zero set, the quotient by its vanishing ideal supplies the labels in
equation (8.2). A scan of the monomials through the point-count bound selects a basis
starting with the unit. The coordinate at this unit, followed by the constant coordinate in
a power basis of the slice field, gives the normalized functional. The number of accepting
matrix-index paths for each exponent vector reduces to the value of that functional.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceEvaluator

open FiniteSlice MonomialBasis Evaluator MvPolynomial

/-- Enumerate all exponent tuples of total degree at most `N`, with the zero tuple
first. Distinct tuples can give the same monomial value in the algebra. -/
theorem exists_monomial_listing {L A : Type*} [Fintype L] [CommRing A] (X : L → A) (N : ℕ) :
    ∃ m, ∃ listing : Fin (m + 1) → A, m + 1 ≤ (N + 1) ^ Fintype.card L ∧
      Set.range listing = monomials X N ∧ listing 0 = 1 := by
  classical
  let B := {e : L → Fin (N + 1) // (∑ i, (e i).val) ≤ N}
  let z : B := ⟨fun _ => 0, by simp⟩
  let m := Fintype.card B - 1
  have hcard : Fintype.card B = m + 1 := by
    have := Fintype.card_pos_iff.mpr (show Nonempty B from ⟨z⟩)
    dsimp [m]
    omega
  let u : Fin (m + 1) ≃ B := (Fintype.equivFinOfCardEq hcard).symm
  let b := (Equiv.swap (0 : Fin (m + 1)) (u.symm z)).trans u
  let val (e : B) := ∏ i, X i ^ (e.val i).val
  refine ⟨m, val ∘ b, ?_, ?_, ?_⟩
  · rw [← hcard]
    simpa only [Fintype.card_fun, Fintype.card_fin] using
      Fintype.card_le_of_injective (Subtype.val : B → (L → Fin (N + 1))) Subtype.val_injective
  · ext a
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨fun i => ((b j).val i).val, (b j).property, rfl⟩
    · rintro ⟨e, hd, rfl⟩
      have hle (i : L) : e i ≤ N :=
        (Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)).trans hd
      let a : B := ⟨fun i => ⟨e i, Nat.lt_succ_of_le (hle i)⟩, hd⟩
      exact ⟨b.symm a, by simp [a, val]⟩
  · simp [b, z, val]

variable {p : ℕ} [Fact p.Prime] {K E : Type*} [Field K] [Fintype K] [Field E]
  [Algebra K E] [Algebra (ZMod p) K] {t : ℕ}

/-- Constant coordinate of the prime-field power basis of the finite slice field. -/
noncomputable def primeCoordinate (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [Fintype K] [Algebra (ZMod p) K] : K →ₗ[ZMod p] ZMod p :=
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod p) K
  pb.basis.coord ⟨0, pb.dim_pos⟩

theorem primeCoordinate_one : primeCoordinate p K 1 = 1 := by
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod p) K
  let u : Fin pb.dim := ⟨0, pb.dim_pos⟩
  have h : pb.basis u = 1 := by simp [pb.basis_eq_pow, u]
  change pb.basis.coord u 1 = 1
  rw [← h, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

/-- The ordered monomial list, the retained independent entries, and the index of the unit. -/
structure Presentation (K : Type*) [Field K] {E : Type*} [Field E] [Algebra K E]
    (I : Ideal (MvPolynomial (Fin t) K)) (N : ℕ) where
  /-- Last valid index in the finite list of monomials used to choose a basis of the coordinate
  algebra. -/
  lastIndex : ℕ
  /-- Enumerate the coordinate monomials through degree `N`, with the constant monomial in
  position zero. -/
  listing : Fin (lastIndex + 1) → CoordinateAlgebra K (zeroLocus E I)
  listing_range : Set.range listing = monomials (coordinateLabel (zeroLocus E I)) N
  first_eq_one : listing 0 = 1
  /-- Basis of the coordinate algebra formed by retaining each listed monomial that increases
  the span of its predecessors. -/
  basis : Module.Basis (RankQuery.greedyIndices K listing) K (CoordinateAlgebra K (zeroLocus E I))
  basis_apply : ∀ i, basis i = listing i.val
  /-- Greedy basis index of the constant monomial one, used to extract its coordinate in the
  normalized functional. -/
  unitIndex : RankQuery.greedyIndices K listing
  unitIndex_val : unitIndex.val = 0

/-- The selected basis of any listing of all bounded monomials beginning with one. -/
theorem evaluator_for_listing (I : Ideal (MvPolynomial (Fin t) K))
    [Fintype (zeroLocus E I)] [Nonempty (zeroLocus E I)] {N m : ℕ}
    (hN : Fintype.card (zeroLocus E I) ≤ N)
    (listing : Fin (m + 1) → CoordinateAlgebra K (zeroLocus E I))
    (hlisting : Set.range listing = monomials (coordinateLabel (zeroLocus E I)) N)
    (hfirst : listing 0 = 1) :
    ∃ d : Presentation K I N (E := E), d.lastIndex = m ∧ HEq d.listing listing := by
  let V := zeroLocus E I
  let A := CoordinateAlgebra K V
  obtain ⟨hfin, hdim⟩ := coordinateAlgebra_finite_finrank (E := E) I
  let : Module.Finite K A := hfin
  let : Nontrivial A := coordinateAlgebra_nontrivial V
  obtain ⟨b, hb, u, hu, _⟩ := prefix_basis (coordinateLabel V) N
    (adjoin_coordinateLabel V) (hdim.trans hN) listing hlisting hfirst
  exact ⟨⟨m, listing, hlisting, hfirst, b, hb, u, hu⟩, rfl, HEq.rfl⟩

variable {I : Ideal (MvPolynomial (Fin t) K)} {N : ℕ}

/-- Coordinate on the unit of the slice algebra followed by the constant coefficient in the
prime-field power basis of the slice field. -/
noncomputable def Presentation.functional (d : Presentation K I N (E := E)) :
    CoordinateAlgebra K (zeroLocus E I) →ₗ[ZMod p] ZMod p :=
  primeFunctional d.basis d.unitIndex (primeCoordinate p K)

/-- Integer number of the evaluator's successful matrix-index paths. -/
noncomputable def Presentation.branchCount (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K]
    (d : Presentation K I N (E := E)) (width : ℕ) (e : Fin t → ℕ) : ℕ :=
  Fintype.card (AcceptingBranches.{0, _, 0} (primeCoordinate p K)
    (transitionMatrices d.basis (digitProgram K (coordinateLabel (zeroLocus E I)) width e))
    d.unitIndex d.unitIndex)

theorem Presentation.functional_one (d : Presentation K I N (E := E)) :
    d.functional (p := p) 1 = 1 := by
  apply primeFunctional_one _ _ _ _ primeCoordinate_one
  rw [d.basis_apply, d.unitIndex_val, d.first_eq_one]

theorem Presentation.branchCount_mod (d : Presentation K I N (E := E))
    (width : ℕ) (e : Fin t → ℕ) (he : ∀ i, e i < 2 ^ width) :
    (d.branchCount p width e : ZMod p) =
      d.functional (∏ i, coordinateLabel (zeroLocus E I) i ^ e i) := by
  apply finiteAlgebra_pathCount _ _ _ _ _ _ _ he
  rw [d.basis_apply, d.unitIndex_val, d.first_eq_one]

/-- Given a finite nonempty slice, one basis and one normalized linear functional count
every exponent vector, at every input width, and the chosen labels solve all the equations.
The monomial listing has at most `(N + 1) ^ t` entries. -/
theorem exists_sliceEvaluator (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K]
    (I : Ideal (MvPolynomial (Fin t) K)) [Fintype (zeroLocus E I)] [Nonempty (zeroLocus E I)]
    {N : ℕ} (hN : Fintype.card (zeroLocus E I) ≤ N) :
    ∃ d : Presentation K I N (E := E), d.lastIndex + 1 ≤ (N + 1) ^ t ∧
      d.functional (p := p) 1 = 1 ∧
      (∀ f ∈ I, MvPolynomial.aeval (coordinateLabel (K := K) (zeroLocus E I)) f = 0) ∧
      ∀ width (e : Fin t → ℕ), (∀ i, e i < 2 ^ width) →
        (d.branchCount p width e : ZMod p) =
          d.functional (∏ i, coordinateLabel (zeroLocus E I) i ^ e i) := by
  obtain ⟨m, list, hbound, hrange, hfirst⟩ := exists_monomial_listing
    (coordinateLabel (K := K) (zeroLocus E I)) N
  obtain ⟨d, hd, _⟩ := evaluator_for_listing I hN list hrange hfirst
  refine ⟨d, by simpa [hd] using hbound, d.functional_one, ?_, d.branchCount_mod⟩
  intro f hf
  rw [aeval_coordinateLabel]
  exact equation_eq_zero I f hf

end SliceEvaluator

end VPVNP
end Computability
end OAI
