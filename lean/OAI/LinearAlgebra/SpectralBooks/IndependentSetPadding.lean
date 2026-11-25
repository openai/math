import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.IndependentSetPolynomial

/-! # Padding a bipartite independent-set polynomial with isolated rows

Specializing the two variables of each new row to its empty- and occupied-state
weights, one and zero, recovers the polynomial on the original graph.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
section

namespace IndependentSetGraph

/-- Successive variable-or-constant substitutions form one projection over the same semiring. -/
theorem project_comp {R σ τ υ : Type*} [CommSemiring R]
    (p : σ → ProjectionAtom R τ) (q : τ → ProjectionAtom R υ) (f : MvPolynomial σ R) :
    project q (project p f) = project (fun x => (p x).elim q Sum.inr) f := by
  unfold project
  rw [MvPolynomial.comp_aeval_apply]
  congr 1
  ext x
  cases h : p x <;> simp [atomPolynomial, h]

end IndependentSetGraph

namespace IndependentSetGrid

open IndependentSetGraph
open scoped Classical BigOperators

variable {m n : ℕ} {R : Type*} [CommSemiring R]

/-- Place all old rows first and add isolated rows at the end. -/
def padded (E : Fin m → Fin n → Prop) (t : ℕ) : Fin (m+t) → Fin n → Prop :=
  Fin.append E (fun _ _ => False)

/-- Force each isolated padding vertex to be unoccupied. -/
def paddingProjection (m n t : ℕ) : ((Fin (m+t) ⊕ Fin n) × Bool) →
    ProjectionAtom R ((Fin m ⊕ Fin n) × Bool)
  | (.inl i, b) => Fin.append (fun j => Sum.inl (.inl j, b))
      (fun _ => Sum.inr (if b then 0 else 1)) i
  | (.inr j, b) => Sum.inl (.inr j, b)

/-- Ignoring the extra bits gives exactly the original edge conditions. -/
theorem independent_padded_iff (E : Fin m → Fin n → Prop) (t : ℕ) (b : Bits (m+t) n) :
    Independent (padded E t) b ↔ Independent E (b.1 ∘ Fin.castAdd t, b.2) := by
  constructor
  · intro h i j hij
    exact h (i.castAdd t) j (by simpa [padded] using hij)
  · intro h i
    induction i using Fin.addCases with
    | left i => simpa [padded] using h i
    | right i => simp [padded]

private def extendBits (t : ℕ) (b : Bits m n) : Bits (m+t) n :=
  (Fin.append b.1 (fun _ => false), b.2)

/-- In the weighted sum, the new rows contribute a single all-false assignment. -/
theorem generatingSum_padded (E : Fin m → Fin n → Prop) (t : ℕ)
    (row : Fin m → Bool → R) (col : Fin n → Bool → R) :
    generatingSum (padded E t) (Fin.append row (fun _ b => if b then 0 else 1)) col =
      generatingSum E row col := by
  classical
  symm
  unfold generatingSum
  apply Fintype.sum_of_injective (extendBits t)
  · intro b b' h
    apply Prod.ext
    · funext i
      simpa [extendBits] using congrArg (fun z : Bits (m+t) n => z.1 (i.castAdd t)) h
    · exact congrArg (fun z : Bits (m+t) n => z.2) h
  · intro b hb
    have hbad : ∃ i : Fin t, b.1 (i.natAdd m) = true := by
      by_contra! h
      apply hb
      refine ⟨(b.1 ∘ Fin.castAdd t, b.2), Prod.ext ?_ rfl⟩
      funext i
      induction i using Fin.addCases with
      | left i => simp [extendBits]
      | right i => simpa [extendBits] using (Bool.eq_false_iff.mpr (h i)).symm
    obtain ⟨i, hi⟩ := hbad
    have hprod : (∏ j : Fin (m+t), (Fin.append row (fun _ b => if b then 0 else 1)) j (b.1 j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (i.natAdd m))
      simp [hi]
    simp [hprod]
  · intro b
    rw [independent_padded_iff, Fin.prod_univ_add]
    have hr : (extendBits t b).1 ∘ Fin.castAdd t = b.1 := by ext i; simp [extendBits]
    rw [hr]
    simp [extendBits]

/-- Projection from the padded polynomial to the original one, keeping both weights
of every original vertex. -/
theorem project_padded_polynomial (E : Fin m → Fin n → Prop) (t : ℕ) :
    project (paddingProjection (R := R) m n t) (polynomial (padded E t)) = polynomial E := by
  classical
  unfold project polynomial
  simp only [generatingSum, map_sum, apply_ite, map_prod, map_mul, map_zero, MvPolynomial.aeval_X]
  convert! generatingSum_padded E t (fun i b => MvPolynomial.X (R := R) (Sum.inl i, b))
    (fun j b => MvPolynomial.X (Sum.inr j, b)) using 1
  unfold generatingSum
  apply Finset.sum_congr rfl
  intro b _
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  induction i using Fin.addCases with
  | left i => simp [paddingProjection, atomPolynomial]
  | right i => cases b.1 (i.natAdd m) <;> simp [paddingProjection, atomPolynomial]

/-- Every term of the grid polynomial contains one variable per row and column. -/
theorem polynomial_isHomogeneous (E : Fin m → Fin n → Prop) :
    (polynomial (R := R) E).IsHomogeneous (m+n) := by
  unfold polynomial generatingSum
  apply MvPolynomial.IsHomogeneous.sum
  intro b _
  split
  · apply MvPolynomial.IsHomogeneous.mul
    · simpa using MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ : Fin m => 1)
        (fun i _ => MvPolynomial.isHomogeneous_X (R := R) (Sum.inl i, b.1 i))
    · simpa using MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ : Fin n => 1)
        (fun j _ => MvPolynomial.isHomogeneous_X (R := R) (Sum.inr j, b.2 j))
  · exact MvPolynomial.isHomogeneous_zero _ _ _

/-- Setting all occupied weights to zero and unoccupied weights to one leaves
only the empty independent set. -/
theorem polynomial_eval_empty (E : Fin m → Fin n → Prop) :
    MvPolynomial.eval (fun x : (Fin m ⊕ Fin n) × Bool => if x.2 then (0 : R) else 1)
      (polynomial E) = 1 := by
  classical
  let empty : Bits m n := (fun _ => false, fun _ => false)
  have hempty : Independent E empty := by simp [Independent, empty]
  unfold polynomial generatingSum
  simp only [map_sum, apply_ite, map_mul, map_prod, MvPolynomial.eval_X, map_zero]
  rw [Finset.sum_eq_single empty]
  · simp [hempty, empty]
  · intro b _ hne
    by_cases hr : ∀ i, b.1 i = false
    · have hc : ∃ j, b.2 j = true := by
        by_contra! h
        exact hne (Prod.ext (funext hr) (funext fun j => Bool.eq_false_iff.mpr (h j)))
      obtain ⟨j, hj⟩ := hc
      have hz : (∏ k, (if b.2 k then (0 : R) else 1)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [hj]
      simp [hz]
    · obtain ⟨i, hi⟩ := not_forall.mp hr
      have hz : (∏ k, (if b.1 k then (0 : R) else 1)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [Bool.eq_true_of_not_eq_false hi]
      simp [hz]
  · simp

/-- The grid polynomial over a nontrivial coefficient semiring has total degree
equal to the number of vertices, including any isolated rows. -/
theorem polynomial_totalDegree [Nontrivial R] (E : Fin m → Fin n → Prop) :
    (polynomial (R := R) E).totalDegree = m+n := by
  apply (polynomial_isHomogeneous E).totalDegree
  intro hz
  simpa [hz] using (polynomial_eval_empty (R := R) E)

end IndependentSetGrid
end

end

end SpectralBooks
end LinearAlgebra
end OAI
