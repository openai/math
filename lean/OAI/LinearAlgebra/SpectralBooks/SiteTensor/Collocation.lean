import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Split

/-! # Collocated exterior operators in the endpoint-coupling recursion

A single exterior wire supplies the row or column at the other endpoint,
regardless of the dimension of the intermediate operator level.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical BigOperators

namespace SiteTensor.Relocation

variable {I J Q H M : Type} {K : Type*} {A : I → Type}
variable [Fintype I] [Fintype J] [∀ i, Fintype (A i)]
variable [Fintype Q] [Fintype H] [Fintype M] [CommSemiring K]

private theorem copy_entry (f : H → K) (z : H) (w : K) :
    w * f z = ∑ m, (w * if m = z then 1 else 0) * f m := by
  simp [mul_ite, ite_mul]

/-- At the column endpoint, compute the entire marked matrix locally and
use one wire to supply its row to the other endpoint. -/
theorem split_restricts_at_column (T : (∀ i, A i) → Q → K)
    (S : (∀ i, A i) → Q → H → H → K) (f : Q → Q → H → H → K)
    (hS : ∀ x i α β, S x i α β = ∑ j, T x j * f i j α β)
    (σ : I → J) (a b : J) :
    ((split A Q H S).group (placeSplit σ a a b)).Restricts
      (((marked A Q T).group (placeMark σ a)).mul (wire K H b a)) := by
  refine restricts_contraction T σ b a _ (fun i x => x ⟨.inl i, rfl⟩)
    (fun x m => if m = x ⟨.inr 2,rfl⟩ then 1 else 0)
    (fun x j m => f (x ⟨.inr 0,rfl⟩) j (x ⟨.inr 1,rfl⟩) m) ?_
  intro x
  refine (hS _ _ _ _).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  exact copy_entry (K := K) (H := H) (fun m => f (x a ⟨.inr 0,rfl⟩) j (x a ⟨.inr 1,rfl⟩) m) _ _

/-- At the row endpoint, the same computation uses the wire for the column. -/
theorem split_restricts_at_row (T : (∀ i, A i) → Q → K)
    (S : (∀ i, A i) → Q → H → H → K) (f : Q → Q → H → H → K)
    (hS : ∀ x i α β, S x i α β = ∑ j, T x j * f i j α β)
    (σ : I → J) (a b : J) :
    ((split A Q H S).group (placeSplit σ b a b)).Restricts
      (((marked A Q T).group (placeMark σ b)).mul (wire K H a b)) := by
  refine restricts_contraction T σ a b _ (fun i x => x ⟨.inl i, rfl⟩)
    (fun x m => if m = x ⟨.inr 1,rfl⟩ then 1 else 0)
    (fun x j m => f (x ⟨.inr 0,rfl⟩) j m (x ⟨.inr 2,rfl⟩)) ?_
  intro x
  refine (hS _ _ _ _).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  exact copy_entry (K := K) (H := H) (fun m => f (x b ⟨.inr 0,rfl⟩) j m (x b ⟨.inr 2,rfl⟩)) _ _

omit [Fintype I] [∀ i, Fintype (A i)] [Fintype H] in
theorem plusCoeff_eq (T : (∀ i, A i) → Q → K) (L : Q → M → H → K) (D : Q → H → M → K)
    (x : ∀ i, A i) (i : Q) (α β : H) :
    plusCoeff T L D x i α β = ∑ j, T x j * ∑ m, L i m α * D j β m := by
  simp only [plusCoeff, Finset.mul_sum, mul_assoc]

omit [Fintype I] [∀ i, Fintype (A i)] [Fintype H] in
theorem minusCoeff_eq (T : (∀ i, A i) → Q → K) (D : Q → M → H → K) (L : Q → H → M → K)
    (x : ∀ i, A i) (i : Q) (α β : H) :
    minusCoeff T D L x i α β = ∑ j, T x j * ∑ m, D j m α * L i β m := by
  simp only [minusCoeff, Finset.mul_sum, mul_assoc]

end SiteTensor.Relocation

end

end SpectralBooks
end LinearAlgebra
end OAI
