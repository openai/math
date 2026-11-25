import OAI.LinearAlgebra.SpectralBooks.TensorSemiring
import Mathlib.Data.Fintype.Option

/-! # Finite tagged sums of basis presentations in the tensor semiring -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

noncomputable section

variable {I : Type*} [Fintype I] [Nonempty I] {K : Type*} [CommSemiring K]

/-- The raw tensor associated with a list of basis terms, allowing repetitions. -/
abbrev basisRaw {S : Type} [Fintype S] {A : I → Type} [∀ i, Fintype (A i)]
    (term : S → ∀ i, A i) : Raw I K :=
  ⟨A, inferInstance, Crossing.basisTensor term⟩

omit [Nonempty I] in
private theorem basisRaw_reindex {S S' : Type} [Fintype S] [Fintype S']
    {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (a : S → ∀ i, A i) (b : S' → ∀ i, B i) (e : S ≃ S') (f : ∀ i, A i ≃ B i)
    (hf : ∀ s i, f i (a s i) = b (e s) i) :
    ofRaw (K := K) (basisRaw a) = ofRaw (basisRaw b) := by
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent f ?_)
  intro (x : ∀ i, A i)
  simp only [basisRaw, Crossing.basisTensor]
  apply Fintype.sum_equiv e
  intro s
  have h : (fun i => f i (x i)) = b (e s) ↔ x = a s := by
    simp only [funext_iff, ← hf, Equiv.apply_eq_iff_eq]
  simp only [h]

private theorem push_basis {S X Y : Type*} [Fintype S] [Fintype X]
    [DecidableEq X] [DecidableEq Y] (f : X → Y) (a : S → X) (y : Y) :
    pushCoeff f (fun x => ∑ s, if x = a s then (1 : K) else 0) y =
      ∑ s, if y = f (a s) then 1 else 0 := by
  unfold pushCoeff
  have hx (x : X) : (if f x = y then ∑ s, if x = a s then (1 : K) else 0 else 0) =
      ∑ s, if x = a s then (if f x = y then 1 else 0) else 0 := by
    by_cases h : f x = y <;> simp [h]
  simp_rw [hx]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp [eq_comm]

private def sumTerm {S R : Type} {A B : I → Type}
    (a : S → ∀ i, A i) (b : R → ∀ i, B i) : S ⊕ R → ∀ i, A i ⊕ B i :=
  Sum.elim (fun s i => .inl (a s i)) (fun r i => .inr (b r i))

omit [Nonempty I] in
private theorem basisRaw_sumTerm {S R : Type} [Fintype S] [Fintype R]
    {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (a : S → ∀ i, A i) (b : R → ∀ i, B i) :
    ofRaw (K := K) (basisRaw (sumTerm a b)) = ofRaw (basisRaw a) + ofRaw (basisRaw b) := by
  rw [← ofRaw_add]
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent (fun i => Equiv.refl (A i ⊕ B i))
  intro (x : ∀ i, A i ⊕ B i)
  let (i : I) : DecidableEq (A i ⊕ B i) := fun _ _ => Classical.propDecidable _
  change Crossing.basisTensor (sumTerm a b) x = sumCoeff (Crossing.basisTensor a) (Crossing.basisTensor b) x
  simp only [Fintype.sum_sum_type, sumCoeff, Crossing.basisTensor]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact (push_basis (K := K) (fun (y : ∀ i, A i) i => (Sum.inl (y i) : A i ⊕ B i)) a x).symm
  · exact (push_basis (K := K) (fun (y : ∀ i, B i) i => (Sum.inr (y i) : A i ⊕ B i)) b x).symm

private def sigmaOption {E : Type} (A : Option E → Type) :
    (Σ l, A l) ≃ A none ⊕ (Σ l, A (some l)) where
  toFun
    | ⟨none, a⟩ => .inl a
    | ⟨some l, a⟩ => .inr ⟨l, a⟩
  invFun
    | .inl a => ⟨none, a⟩
    | .inr ⟨l, a⟩ => ⟨some l, a⟩
  left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
  right_inv := by rintro (_ | ⟨_, _⟩) <;> rfl

/-- Tagging the basis terms at every site represents the sum of their tensor classes. -/
theorem ofRaw_sumBasis {E : Type} [Fintype E] {S : E → Type}
    [∀ l, Fintype (S l)] {A : E → I → Type} [∀ l i, Fintype (A l i)]
    (term : ∀ l, S l → ∀ i, A l i) :
    ofRaw (K := K) (basisRaw (Crossing.sumBasis term)) = ∑ l, ofRaw (basisRaw (term l)) := by
  revert term
  let P (E : Type) [Fintype E] := ∀ {S : E → Type} [∀ l, Fintype (S l)]
    {A : E → I → Type} [∀ l i, Fintype (A l i)] (term : ∀ l, S l → ∀ i, A l i),
    ofRaw (K := K) (basisRaw (Crossing.sumBasis term)) = ∑ l, ofRaw (basisRaw (term l))
  apply (show P E from ?_)
  apply Fintype.induction_empty_option (P := fun E _ => P E)
  · intro α β _ e ih S _ A _ term
    let : Fintype α := Fintype.ofEquiv β e.symm
    let t (l : α) := term (e l)
    calc
      _ = ofRaw (K := K) (basisRaw (Crossing.sumBasis t)) := Eq.symm <|
        basisRaw_reindex _ _ (Equiv.sigmaCongrLeft e) (fun i => Equiv.sigmaCongrLeft (β := fun l => A l i) e)
          (fun _ _ => rfl)
      _ = _ := (ih t).trans (Fintype.sum_equiv e _ _ (fun _ => rfl))
  · intro S _ A _ term
    rw [Fintype.sum_empty]
    change ofRaw _ = ofRaw (Raw.zero I K)
    apply ofRaw_eq_iff.mpr
    apply Raw.reindex_equivalent (fun i => Equiv.equivOfIsEmpty (Σ l, A l i) PEmpty)
    intro x
    exact isEmptyElim ((x (Classical.arbitrary I)).1)
  · intro α _ ih S _ A _ term
    let t (l : α) := term (some l)
    rw [Fintype.sum_option]
    calc
      _ = ofRaw (K := K) (basisRaw (sumTerm (term none) (Crossing.sumBasis t))) := by
        apply basisRaw_reindex _ _ (sigmaOption S) (fun i => sigmaOption (fun l => A l i))
        rintro ⟨_ | _, _⟩ _ <;> rfl
      _ = _ := by rw [basisRaw_sumTerm, ih t]

end

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
