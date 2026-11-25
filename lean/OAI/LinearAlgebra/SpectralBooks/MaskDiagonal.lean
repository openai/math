import OAI.LinearAlgebra.SpectralBooks.TensorSemiring

/-! # Common-label diagonals in a fixed space of sites

On the support a local basis index is a label. Off the support the local
space has one basis index. The type of functions from the membership
proposition implements both cases in one coordinate format.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

open scoped Classical

variable {I : Type*} [Fintype I]

abbrev MaskLeg (S : Finset I) (α : Type) (i : I) := i ∈ S → α

/-- A partial diagonal in the ambient site set `I`. -/
noncomputable def Raw.maskDiagonal (K : Type*) [Field K] (S : Finset I) (α : Type) [Fintype α] :
    Raw.{0} I K :=
  ⟨MaskLeg S α, fun _ ↦ Fintype.ofFinite _, Crossing.basisTensor (fun (a : α) i (_ : i ∈ S) ↦ a)⟩

/-- Pairing independent terms in two basis presentations is multiplication
in the tensor semiring, up to the indicated local changes of coordinates. -/
theorem basisTensor_paired_eq_mul {K : Type*} [Field K]
    {A B C : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]
    {J L : Type} [Fintype J] [Fintype L] (a : J → ∀ i, A i) (b : L → ∀ i, B i)
    (c : J × L → ∀ i, C i) (e : ∀ i, C i ≃ A i × B i)
    (h : ∀ s t i, e i (c (s,t) i) = (a s i, b t i)) :
    ofRaw (I := I) (K := K) ⟨C, inferInstance, Crossing.basisTensor c⟩ =
      ofRaw (I := I) (K := K) ⟨A, inferInstance, Crossing.basisTensor a⟩ *
        ofRaw (I := I) (K := K) ⟨B, inferInstance, Crossing.basisTensor b⟩ := by
  classical
  rw [← ofRaw_mul]
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent e
  intro x
  change Crossing.basisTensor c x = Crossing.basisTensor a (fun i ↦ (e i (x i)).1) *
    Crossing.basisTensor b (fun i ↦ (e i (x i)).2)
  simp only [Crossing.basisTensor, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  have heq : x = c (s, t) ↔ ((fun i ↦ (e i (x i)).1) = a s ∧
      (fun i ↦ (e i (x i)).2) = b t) := by
    constructor
    · rintro rfl
      exact ⟨funext fun i ↦ congrArg Prod.fst (h s t i), funext fun i ↦ congrArg Prod.snd (h s t i)⟩
    · rintro ⟨ha,hb⟩
      funext i
      exact (e i).injective ((Prod.ext (congrFun ha i) (congrFun hb i)).trans (h s t i).symm)
  by_cases ha : (fun i ↦ (e i (x i)).1) = a s <;> simp [heq, ha]

/-- A basis presentation with two independent labels factors into the partial
diagonals on the supports where the labels are read. -/
theorem basisTensor_eq_maskDiagonal_mul {K : Type*} [Field K]
    {C : I → Type} [∀ i, Fintype (C i)] {J L : Type} [Fintype J] [Fintype L]
    (S T : Finset I) (c : J × L → ∀ i, C i)
    (e : ∀ i, C i ≃ MaskLeg S J i × MaskLeg T L i)
    (h : ∀ s t i, e i (c (s,t) i) = (fun _ ↦ s, fun _ ↦ t)) :
    ofRaw (I := I) (K := K) ⟨C, inferInstance, Crossing.basisTensor c⟩ =
      ofRaw (Raw.maskDiagonal K S J) * ofRaw (Raw.maskDiagonal K T L) := by
  let (i : I) : Fintype (MaskLeg S J i) := (Raw.maskDiagonal K S J).finiteLeg i
  let (i : I) : Fintype (MaskLeg T L i) := (Raw.maskDiagonal K T L).finiteLeg i
  exact basisTensor_paired_eq_mul (K := K) (A := MaskLeg S J) (B := MaskLeg T L)
    (fun a _ _ ↦ a) (fun b _ _ ↦ b) c e h

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
