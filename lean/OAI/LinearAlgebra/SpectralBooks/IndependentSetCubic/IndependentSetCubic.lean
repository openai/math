import OAI.LinearAlgebra.SpectralBooks.IndependentSetCubic.IndependentSetCubicShape
import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.IndependentSetPolynomial

/-! # The cubic projection for homogeneous independent-set polynomials

The first copy retains the variable pair of the original vertex, the other
copies have unit weight, and each of the two internal vertices of a link
receives the signed pair `(1,-1)`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace IndependentSetCubic

open scoped Classical BigOperators
open IndependentSetGraph (independent weightedSum)
variable {V E R : Type*} [Fintype V] [Fintype E] [CommRing R] (l r : E → V)

/-- The original unary table appears on the zeroth copy in each chain. -/
def weights (w : V → Bool → R) : Vertex l r → Bool → R
  | .inl ⟨v, i⟩, b => if i = 0 then w v b else 1
  | .inr _, b => signWeight b

private theorem sum_split {A B M : Type*} [Fintype (A ⊕ B → Bool)]
    [Fintype (A → Bool)] [Fintype (B → Bool)] [AddCommMonoid M]
    (f : (A ⊕ B → Bool) → M) :
    (∑ z, f z) = ∑ a, ∑ b, f (Sum.elim a b) := by
  rw [← (Equiv.sumArrowEquivProdArrow A B Bool).symm.sum_comp f, Fintype.sum_prod_type]
  rfl

omit [Fintype V] in
private theorem independent_iff (c : Copies (incidenceDegree l r) → Bool)
    (p q : Links (incidenceDegree l r) → Bool) :
    independent (left l r) (right l r) (Sum.elim c (Sum.elim p q)) ↔
      (∀ e, c (port l r (.inl e)) = true → c (port l r (.inr e)) ≠ true) ∧
        ∀ j, pathCompatible (c (prev j)) (p j) (q j) (c (nextCopy j)) := by
  unfold independent pathCompatible
  simp only [Sum.forall, left, right, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨h, h₁, h₂, h₃⟩
    exact ⟨h, fun j => ⟨h₁ j, h₂ j, h₃ j⟩⟩
  · rintro ⟨h, hlinks⟩
    exact ⟨h, fun j => (hlinks j).1, fun j => (hlinks j).2.1, fun j => (hlinks j).2.2⟩

private theorem prod_weights (w : V → Bool → R) (c : Copies (incidenceDegree l r) → Bool)
    (p q : Links (incidenceDegree l r) → Bool) :
    (∏ v : Vertex l r, weights l r w v (Sum.elim c (Sum.elim p q) v)) =
      (∏ v, w v (c ⟨v, 0⟩)) * ((∏ j, signWeight (p j)) * ∏ j, signWeight (q j)) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sigma]
  congr 2
  funext v
  rw [Fin.prod_univ_succ]
  simp [weights]

/-- Specialize the cubic graph's weights to recover the original graph sum. -/
theorem weightedSum_eq (w : V → Bool → R) :
    weightedSum (left l r) (right l r) (weights l r w) = weightedSum l r w := by
  let d := incidenceDegree l r
  let F (c : Copies d → Bool) : R :=
    if ∀ e, c (port l r (.inl e)) = true → c (port l r (.inr e)) ≠ true
    then ∏ v, w v (c ⟨v, 0⟩) else 0
  let : DecidableEq (Vertex l r) := fun a b => Classical.propDecidable (a = b)
  unfold weightedSum
  let g (b : Vertex l r → Bool) := if independent (left l r) (right l r) b then
    ∏ v, weights l r w v (b v) else 0
  calc
    _ = ∑ c : Copies d → Bool, ∑ a : Links d ⊕ Links d → Bool, g (Sum.elim c a) :=
      @sum_split (Copies d) (Links d ⊕ Links d) R _ _ _ _ g
    _ = ∑ c : Copies d → Bool, ∑ p : Links d → Bool, ∑ q : Links d → Bool,
      g (Sum.elim c (Sum.elim p q)) :=
      Finset.sum_congr rfl fun c _ =>
        @sum_split (Links d) (Links d) R _ _ _ _ (fun a => g (Sum.elim c a))
    _ = ∑ c : Copies d → Bool, ∑ p : Links d → Bool, ∑ q : Links d → Bool,
          if ∀ j, pathCompatible (c (prev j)) (p j) (q j) (c (nextCopy j)) then
            F c * (∏ j, signWeight (p j)) * ∏ j, signWeight (q j) else 0 := by
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun p _ =>
        Finset.sum_congr rfl fun q _ => ?_
      simp only [g, independent_iff, prod_weights, F]
      split_ifs <;> simp_all [mul_assoc]
      dsimp [d] at *
    _ = ∑ x : V → Bool, F (fun j => x j.1) := contract_paths d F
    _ = _ := by simp [F, independent, flagVertex]

/-- The substitution of variable pairs and constants is an integral p-projection. -/
def projection : Vertex l r × Bool → IndependentSetGraph.ProjectionAtom R (V × Bool)
  | (.inl ⟨v, i⟩, b) => if i = 0 then .inl (v,b) else .inr 1
  | (.inr _, b) => .inr (signWeight b)

theorem project_polynomial :
    IndependentSetGraph.project (projection (R := R) l r)
        (IndependentSetGraph.polynomial R (left l r) (right l r)) =
      IndependentSetGraph.polynomial R l r := by
  rw [IndependentSetGraph.project_polynomial]
  unfold IndependentSetGraph.polynomial
  convert weightedSum_eq l r (fun v b => (MvPolynomial.X (v, b) : MvPolynomial (V × Bool) R)) using 2
  funext v b
  rcases v with ⟨v, i⟩ | j
  · by_cases h : i = 0 <;> simp [projection, weights, IndependentSetGraph.atomPolynomial, h]
  · cases b <;> simp [projection, weights, signWeight, IndependentSetGraph.atomPolynomial]

end IndependentSetCubic

end

end SpectralBooks
end LinearAlgebra
end OAI
