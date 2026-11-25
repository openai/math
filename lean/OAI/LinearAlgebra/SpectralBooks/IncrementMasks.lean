import OAI.LinearAlgebra.SpectralBooks.IncrementRestriction
import OAI.LinearAlgebra.SpectralBooks.MaskDiagonal
import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary

/-! # Factoring the source and target of the common-label degeneration

In the ambient site set the three masks are the intersection `I`, the old
sites `A`, and `I ∪ {z}`. The fourth mask, `A ∪ {z}`, is the full site set.
The two independent labels in each basis presentation give the product of
the corresponding partially supported diagonal classes.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open SiteTensor

/-- The old sites that receive both labels. -/
def incrementJointMask (k m : ℕ) : Finset (IncrementSite k m) :=
  Finset.univ.map Function.Embedding.inl

/-- The occupied sites before inserting the new site. -/
def incrementOldMask (k m : ℕ) : Finset (IncrementSite k m) :=
  Finset.univ.erase (.inr none)

/-- The sites on which the auxiliary label is initially supplied. -/
def incrementAuxMask (k m : ℕ) : Finset (IncrementSite k m) :=
  insert (.inr none) (incrementJointMask k m)

private def bothLabels {α β : Type} {P Q : Prop} (h : P) (k : Q) :
    α × β ≃ (P → α) × (Q → β) where
  toFun x := (fun _ ↦ x.1, fun _ ↦ x.2)
  invFun x := (x.1 h, x.2 k)
  left_inv _ := rfl
  right_inv _ := rfl

private def leftLabel {α β : Type} {P Q : Prop} (h : P) (k : ¬Q) :
    α ≃ (P → α) × (Q → β) where
  toFun a := (fun _ ↦ a, fun z ↦ (k z).elim)
  invFun x := x.1 h
  left_inv _ := rfl
  right_inv _ := Prod.ext rfl (funext fun z ↦ (k z).elim)

private def rightLabel {α β : Type} {P Q : Prop} (h : ¬P) (k : Q) :
    β ≃ (P → α) × (Q → β) where
  toFun b := (fun z ↦ (h z).elim, fun _ ↦ b)
  invFun x := x.2 k
  left_inv _ := rfl
  right_inv _ := Prod.ext (funext fun z ↦ (h z).elim) rfl

private def sourceLegEquiv (q k m L : ℕ) (i : IncrementSite k m) : incrementOldInput q k m L i ≃
    MaskLeg (incrementOldMask k m) (Fin q) i × MaskLeg (incrementAuxMask k m) (Fin L) i := by
  rcases i with j | j
  · exact bothLabels (by simp [incrementOldMask]) (by simp [incrementAuxMask, incrementJointMask])
  · cases j with
    | none => exact rightLabel (by simp [incrementOldMask]) (by simp [incrementAuxMask])
    | some j => exact leftLabel (by simp [incrementOldMask]) (by simp [incrementAuxMask, incrementJointMask])

private def targetLegEquiv (q k m : ℕ) (i : IncrementSite k m) : incrementSiteOutput q k m i ≃
    MaskLeg Finset.univ (Fin q) i × MaskLeg (incrementJointMask k m) (Fin q) i := by
  rcases i with j | j
  · exact bothLabels (Finset.mem_univ _) (by simp [incrementJointMask])
  · exact leftLabel (Finset.mem_univ _) (by simp [incrementJointMask])

/-- The supplied tensor is the product of the old and auxiliary diagonals. -/
theorem ofCoeffs_incrementSourceBasis (K : Type*) [Field K] (q k m L : ℕ) :
    ofCoeffs (Crossing.basisTensor (F := K) (incrementSourceBasis q k m L)) =
      ofRaw (Raw.maskDiagonal K (incrementOldMask k m) (Fin q)) *
        ofRaw (Raw.maskDiagonal K (incrementAuxMask k m) (Fin L)) := by
  classical
  apply basisTensor_eq_maskDiagonal_mul (K := K) (incrementOldMask k m) (incrementAuxMask k m)
    (incrementSourceBasis q k m L) (sourceLegEquiv q k m L)
  intro s t i
  rcases i with j | j
  · rfl
  · cases j with
    | none => exact Prod.ext (funext fun h ↦ by simp [incrementOldMask] at h) rfl
    | some j => exact Prod.ext rfl (funext fun h ↦ by simp [incrementAuxMask, incrementJointMask] at h)

/-- On the target, the first independent label occurs at all sites and the
second independent label occurs precisely in the intersection. -/
theorem ofCoeffs_incrementTargetBasis (K : Type*) [Field K] (q k m : ℕ) :
    ofCoeffs (Crossing.basisTensor (F := K) (incrementTargetBasis q k m)) =
      ofRaw (Raw.maskDiagonal K (Finset.univ : Finset (IncrementSite k m)) (Fin q)) *
        ofRaw (Raw.maskDiagonal K (incrementJointMask k m) (Fin q)) := by
  classical
  apply basisTensor_eq_maskDiagonal_mul (K := K) Finset.univ (incrementJointMask k m)
    (incrementTargetBasis q k m) (targetLegEquiv q k m)
  intro s t i
  rcases i with j | j
  · rfl
  · exact Prod.ext rfl (funext fun h ↦ by simp [incrementJointMask] at h)

end SpectralBooks
end LinearAlgebra
end OAI
