import OAI.LinearAlgebra.SpectralBooks.ParseCircuit

/-! # Coefficient queries for the signed universal polynomial

An input word selects one variable from each pair. Projecting to the coordinates
of these monomials recovers the signed path sums, also for points in an image closure.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MvPolynomial

noncomputable section

/-- The degree-`n` monomial selecting the variable `Z_{i,x_i}` at every position. -/
def signedQueryMonomial {n : ℕ} (x : Fin n → Bool) : DegreeMonomial (Fin n × Bool) n :=
  ⟨∑ i, Finsupp.single (i, x i) 1, by simp [map_sum, Finsupp.degree_single]⟩

theorem signedQueryMonomial_apply {n : ℕ} (x : Fin n → Bool) (i : Fin n) (b : Bool) :
    (signedQueryMonomial x).val (i, b) = if x i = b then 1 else 0 := by
  classical
  simp only [signedQueryMonomial, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · simp [Finsupp.single_apply, Prod.mk.injEq]
  · intro j _ hji
    simp [Prod.mk.injEq, hji]
  · simp

theorem signedQueryMonomial_injective (n : ℕ) :
    Function.Injective (signedQueryMonomial (n := n)) := by
  intro x y h
  funext i
  have hi := congrArg (fun m : DegreeMonomial (Fin n × Bool) n ↦ m.val (i, x i)) h
  simpa [signedQueryMonomial_apply, eq_comm] using hi

/-- The addressed coefficient is exactly the signed path count, reduced in the given ring. -/
theorem coeff_signedWitnessPolynomial (R : Type*) [CommRing R] {n : ℕ} (x : Fin n → Bool) :
    (signedWitnessPolynomial R n).coeff (signedQueryMonomial x).val = (signedWitness x : R) := by
  classical
  have term (y : Fin n → Bool) :
      C (signedWitness y : R) * ∏ i, X (i, y i) =
        monomial (signedQueryMonomial y).val (signedWitness y : R) :=
    (monomial_sum_index _ _ _).symm
  have eq {y z : Fin n → Bool} :
      (signedQueryMonomial y).val = (signedQueryMonomial z).val ↔ y = z :=
    Subtype.val_injective.eq_iff.trans (signedQueryMonomial_injective n).eq_iff
  simp only [signedWitnessPolynomial, coeff_sum, term, coeff_monomial, eq]
  simp

/-- Coordinate selection sends a point in an affine Zariski closure into the closure
of the selected coordinates of the original set. -/
theorem selectedCoordinates_mem_closure {K ι τ : Type*} [Field K] (f : τ → ι)
    {S : Set (ι → K)} {x : ι → K} (hx : x ∈ zeroLocus K (vanishingIdeal K S)) :
    x ∘ f ∈ zeroLocus K (vanishingIdeal K ((fun y : ι → K ↦ y ∘ f) '' S)) := by
  intro p hp
  change eval (x ∘ f) p = 0
  rw [← eval_rename f x p]
  apply hx
  intro y hy
  change eval y (rename f p) = 0
  rw [eval_rename]
  exact hp _ ⟨y, hy, rfl⟩

/-- Any full coefficient closure containing the witness projects to a closure containing
the vector of signed path sums. -/
theorem signedQueries_mem_closure {K : Type*} [Field K] {n : ℕ}
    {S : Set (DegreeMonomial (Fin n × Bool) n → K)}
    (h : degreeCoefficientVector n (signedWitnessPolynomial K n) ∈
      zeroLocus K (vanishingIdeal K S)) :
    (fun x : Fin n → Bool ↦ (signedWitness x : K)) ∈ zeroLocus K
      (vanishingIdeal K ((fun y ↦ y ∘ signedQueryMonomial) '' S)) := by
  simpa only [Function.comp_def, degreeCoefficientVector, coeff_signedWitnessPolynomial] using
    selectedCoordinates_mem_closure signedQueryMonomial h

/-- The integral parse-table coefficient polynomial queried by an input word. -/
def signedQueryCoordinate {n : ℕ} (s : ℕ) (x : Fin n → Bool) :
    MvPolynomial (ParseParameter n (Fin (3*s+3)) (Fin n × Bool)) ℤ :=
  parseCoordinates n (0 : Fin (3*s+3)) (signedQueryMonomial x)

/-- A small circuit in the border model places the signed path counts in the closure of
the simultaneous evaluations of the integral query polynomials. -/
theorem signedQueries_mem_parseClosure (F : Type*) [Field F] {n s : ℕ}
    (hn : 0 < n) (hs : degreeBorderSize n (signedWitnessPolynomial F n) ≤ s) :
    (fun x : Fin n → Bool ↦ (signedWitness x : AlgebraicClosure F)) ∈
      zeroLocus (AlgebraicClosure F) (vanishingIdeal (AlgebraicClosure F)
        (Set.range fun a : ParseParameter n (Fin (3*s+3)) (Fin n × Bool) → AlgebraicClosure F ↦
          fun x ↦ eval₂ (Int.castRingHom (AlgebraicClosure F)) a (signedQueryCoordinate s x))) := by
  have h := signedQueries_mem_closure (signedWitness_mem_parseClosure F hn hs)
  simpa only [parseImage, ← Set.range_comp, Function.comp_def, signedQueryCoordinate] using h

end

end SpectralBooks
end LinearAlgebra
end OAI
