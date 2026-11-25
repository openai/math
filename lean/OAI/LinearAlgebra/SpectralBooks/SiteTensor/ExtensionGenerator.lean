import OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionStar
import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct
import OAI.LinearAlgebra.SpectralBooks.SpectralSpace

/-! # Factoring the two wires incident to a new party -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace SiteTensor

variable {I : Type*} (K : Type*) [Field K]

private abbrev wireFiber (a : I) (s : Option I) :=
  {j : Fin 2 // ![none, some a] j = s}

private theorem wireFiber_ext (a : I) (s : Option I) (u v : wireFiber a s) : u = v := by
  apply Subtype.ext
  have h := u.property.trans v.property.symm
  rcases u with ⟨u, _⟩
  rcases v with ⟨v, _⟩
  fin_cases u <;> fin_cases v <;> simp_all

private theorem wireFiber_eq {a i : I} (j : wireFiber a (some i)) : i = a := by
  obtain ⟨j, h⟩ := j
  fin_cases j <;> simp_all

private def newLegEquiv (a : I) (A : Type) (s : Option I) :
    Option.rec A (fun i ↦ i = a → A) s ≃ (wireFiber a s → A) :=
  match s with
  | none =>
    { toFun := fun x _ ↦ x
      invFun := fun f ↦ f ⟨0, rfl⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun f ↦ funext fun j ↦ congrArg f (wireFiber_ext _ _ _ j) }
  | some i =>
    { toFun := fun f j ↦ f (wireFiber_eq j)
      invFun := fun g hi ↦ g ⟨1, by subst i; rfl⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun f ↦ funext fun j ↦ congrArg f (wireFiber_ext _ _ _ j) }

private theorem twoDiagonal_coeff (A : Type) [Fintype A] (x : Fin 2 → A) :
    (Raw.diagonal (Fin 2) K A).coeff x = if x 0 = x 1 then 1 else 0 := by
  rw [Raw.diagonal_coeff_at (1 : Fin 2)]
  simp [Fin.forall_fin_two]

/-- Pairing the labels at the common new party and at each old party gives
the product of the independently grouped endpoint wires. -/
theorem ofRaw_newStar [Fintype I] (a b : I) (A B : Type) [Fintype A] [Fintype B] :
    ofRaw (Raw.newStar K a b A B) =
      ofRaw ((Raw.diagonal (Fin 2) K A).group ![none, some a]) *
      ofRaw ((Raw.diagonal (Fin 2) K B).group ![none, some b]) := by
  let W (i : I) (D : Type) [Fintype D] := (Raw.diagonal (Fin 2) K D).group ![none, some i]
  let e (s : Option I) : (Raw.newStar K a b A B).Leg s ≃ ((W a A).mul (W b B)).Leg s :=
    match s with
    | none => (newLegEquiv a A none).prodCongr (newLegEquiv b B none)
    | some i => (newLegEquiv a A (some i)).prodCongr (newLegEquiv b B (some i))
  rw [← ofRaw_mul]
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  let u (j : Fin 2) : A := (e (![none, some a] j) (x _)).1 ⟨j, rfl⟩
  let v (j : Fin 2) : B := (e (![none, some b] j) (x _)).2 ⟨j, rfl⟩
  change _ = (Raw.diagonal (Fin 2) K A).coeff u * (Raw.diagonal (Fin 2) K B).coeff v
  rw [twoDiagonal_coeff K A u, twoDiagonal_coeff K B v]
  rfl

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
