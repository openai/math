import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Split
import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct

/-! # The identity term of an exterior split

Separating the two exterior labels into a wire identifies the grouped identity
term with the product of the original marked tensor and the placed diagonal.
The local coordinate identifications allow all three sites to coincide.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace SiteTensor.Relocation

variable {I J Q : Type} {K : Type*} {A : I → Type}
variable [Fintype I] [Fintype J] [Fintype Q] [∀ i, Fintype (A i)] [CommSemiring K]

/-- Grouping a marked coefficient array tensored with an identity factors
sitewise into the marked array and its independent wire. -/
theorem grouped_split_eq_mul (T : (∀ i, A i) → Q → K) (H : Type) [Fintype H] [DecidableEq H]
    (σ : I → J) (c a b : J) :
    ofRaw ((split A Q H (fun x i α β => T x i * if α = β then 1 else 0)).group
      (placeSplit σ c a b)) =
      ofRaw ((marked A Q T).group (placeMark σ c)) * ofRaw (wire K H a b) := by
  let S := (split A Q H (fun x i α β => T x i * if α = β then 1 else 0)).group
    (placeSplit σ c a b)
  let U := (marked A Q T).group (placeMark σ c)
  let W := wire K H a b
  let mark (j : J) (x : S.Leg j) : U.Leg j := fun t => match t with
    | ⟨.inl i,h⟩ => x ⟨.inl i,h⟩
    | ⟨.inr (),h⟩ => x ⟨.inr 0,h⟩
  let ends (j : J) (x : S.Leg j) : W.Leg j := fun ⟨t,h⟩ =>
    match t,h with
    | 0,h => x ⟨.inr 1,h⟩
    | 1,h => x ⟨.inr 2,h⟩
  let join (j : J) (y : U.Leg j × W.Leg j) : S.Leg j := fun t => match t with
    | ⟨.inl i,h⟩ => y.1 ⟨.inl i,h⟩
    | ⟨.inr 0,h⟩ => y.1 ⟨.inr (),h⟩
    | ⟨.inr 1,h⟩ => y.2 ⟨0,h⟩
    | ⟨.inr 2,h⟩ => y.2 ⟨1,h⟩
  let e (j : J) : S.Leg j ≃ (U.mul W).Leg j := {
    toFun := fun x => (mark j x, ends j x)
    invFun := join j
    left_inv := by
      intro x
      funext ⟨k,h⟩
      rcases k with i | i
      · rfl
      · fin_cases i <;> rfl
    right_inv := by
      intro y
      apply Prod.ext
      · funext ⟨k,h⟩
        rcases k with i | ⟨⟩ <;> rfl
      · funext ⟨i,h⟩
        fin_cases i <;> rfl }
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  let labels (t : Fin 2) : H := (ends _ (x (![a,b] t))) ⟨t,rfl⟩
  change _ * (if labels 0 = labels 1 then (1 : K) else 0) =
    _ * (Raw.diagonal (Fin 2) K H).coeff labels
  congr 1
  rw [Raw.diagonal_coeff_at (K := K) (1 : Fin 2) labels]
  congr 1
  exact propext ⟨fun h i => by fin_cases i <;> first | exact h | rfl, fun h => h 0⟩

end SiteTensor.Relocation

end

end SpectralBooks
end LinearAlgebra
end OAI
