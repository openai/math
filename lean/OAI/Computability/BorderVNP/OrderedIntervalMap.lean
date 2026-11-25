import OAI.Computability.BorderVNP.OrderedMatrixComponents

/-!
# Degree-coordinate maps for specialization to words

Reading a fixed target word after marking the source degree is a linear function
of the source coefficients. This supplies the map on affine spaces used in the
closure step of Lemma 13.1.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Ordered

variable {K E σ τ : Type*} [Field K] [Field E]

/-- The coordinate polynomial of one target word after source-degree marking. -/
noncomputable def wordCoordinate [Fintype σ] (d e : ℕ) (v : σ → WordPoly K τ)
    (w : Fin e → τ) : MvPolynomial (Fin d → σ) K :=
  ∑ a : Fin d → σ, MvPolynomial.X a * MvPolynomial.C ((FreeMonoid.lift v (word a)).coeff (word w))

/-- The affine coordinate map agrees with marking the input and reading its output words. -/
theorem eval_wordCoordinate [Fintype σ] (d e : ℕ) (v : σ → WordPoly K τ)
    (p : WordPoly K σ) :
    (fun w => MvPolynomial.eval (coefficients d p) (wordCoordinate d e v w)) =
      coefficients e (markedComponent d v p) := by
  classical
  funext w
  rw [markedComponent_eq_sum]
  simp [wordCoordinate, coefficients, MonoidAlgebra.coeff_smul, Finsupp.finsetSum_apply]

/-- Scalar extension of the row-ordered permanent or determinant is the same family
with coefficients in the extended field. -/
theorem map_rowPolynomial (f : K →+* E) (n : ℕ) (signed : Bool) :
    MonoidAlgebra.mapRingHom (FreeMonoid (Fin n × Fin n)) f (rowPolynomial K n signed) =
      rowPolynomial E n signed := by
  simp [rowPolynomial, map_sum, apply_ite f]

/-- The row-ordered permutation sums have only words of length `n` in their support. -/
theorem rowPolynomial_word_length (n : ℕ) (signed : Bool) (w : FreeMonoid (Fin n × Fin n))
    (hw : w ∈ (rowPolynomial K n signed).coeff.support) : w.toList.length = n := by
  classical
  by_contra hn
  apply Finsupp.mem_support_iff.mp hw
  change (∑ π : Equiv.Perm (Fin n), MonoidAlgebra.single (word fun i => (i, π i))
    (if signed then (((Equiv.Perm.sign π : ℤˣ) : ℤ) : K) else 1)).coeff w = 0
  have hz (π : Equiv.Perm (Fin n)) : word (fun i => (i,π i)) ≠ w :=
    fun h => hn (by rw [← h]; simp [word])
  simp [hz, Finsupp.finsetSum_apply]

/-- Marked substitution of the output is evaluation of the same shared program
in the marker polynomial algebra. -/
theorem marked_word_output {s : ℕ} (c : VPVNP.Circuit K σ s)
    (v : σ → WordPoly K τ) (d : ℕ) :
    markedComponent d v (output c) =
      (c.eval (algebraMap K (Polynomial (WordPoly K τ)))
        (fun x => Polynomial.C (v x) * Polynomial.X)).coeff d := by
  let y := fun x => Polynomial.C (v x) * Polynomial.X
  unfold markedComponent output
  change ((substitute y).toRingHom (c.eval _ _)).coeff d = _
  rw [c.eval_hom]
  apply congrArg (fun g : Polynomial _ => g.coeff d)
  congr 1
  · funext r
    simp [y, substitute, MonoidAlgebra.lift_single, Algebra.smul_def]
  · funext x
    simp [y, substitute, MonoidAlgebra.lift_single]

end Ordered

end BorderVNP
end Computability
end OAI
