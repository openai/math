import OAI.LinearAlgebra.SpectralBooks.Fermion.WickFiniteExpansion
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickNormalMatrix
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickReversalTerms

/-! # The finite supercommutator as a single sum over matchings

Reversing the second Wick expansion matches its terms with those of the first.
The unmatched normal matrix entry is common to both terms, leaving the difference
of their scalar kernel products.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Fermion

/-- An entry of the supercommutator is the sum of its signed matching contributions. -/
theorem supercommutator_apply_eq_sum (N : ℕ) (l r : List FieldLabel) (α β : FockState N) :
    let n := normal (LaurentPolynomial ℤ) (creationField N) (annihilationField N)
    (n l * n r - (-1 : LaurentPolynomial ℤ) ^ (l.length * r.length) • (n r * n l)) α β =
      ∑ p : Matching l r,
        (p.weight (contractionPolynomial N) - p.weight (fun x y ↦ -contractionPolynomial N y x)) *
          mixedNormal p.residual α.val β.val := by
  let n := normal (LaurentPolynomial ℤ) (creationField N) (annihilationField N)
  have h lr rr : n lr * n rr = wickSum (contractionPolynomial N) n lr rr :=
    finite_normal_mul_normal N lr rr
  have hrev := wickSum_reverse _ _ (creationField_anticommute N) (annihilationField_anticommute N)
    (contractionPolynomial N) r l
  rw [Nat.mul_comm r.length l.length] at hrev
  change (n l * n r - _ • (n r * n l)) α β = _
  rw [h, h, ← hrev]
  simp only [wickSum, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  change _ * n p.residual α β - _ * n p.residual α β = _
  rw [← sub_mul, show n p.residual α β = mixedNormal p.residual α.val β.val from normal_matrix_apply ..]

/-- The entrywise matching expansion for the forward block at one and the second
block at the Laurent indeterminate. -/
theorem fieldMatrix_commutator_apply (N : ℕ) (i j : State) (α β : FockState N) :
    (fieldMatrix N false i * fieldMatrix N true j) α β -
        (-1 : LaurentPolynomial ℤ) ^ (i.card * j.card) *
          (fieldMatrix N true j * fieldMatrix N false i) α β =
      ∑ p : Matching (fieldWord false i) (fieldWord true j),
        (p.weight (contractionPolynomial N) - p.weight (fun x y ↦ -contractionPolynomial N y x)) *
          mixedNormal p.residual α.val β.val := by
  have word_length (s : Bool) (I : State) : (fieldWord s I).length = I.card := by
    simp [fieldWord]
  simpa only [fieldMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, word_length] using
    supercommutator_apply_eq_sum N (fieldWord false i) (fieldWord true j) α β

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
