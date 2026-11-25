import OAI.LinearAlgebra.SpectralBooks.MarkedRelocation
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Nodes

/-! # Reindexing an exterior child as a new two-mark node -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace SiteTensor.Relocation
namespace WireNode

variable {K : Type*} [Field K] {J : Type} [Fintype J] [Nonempty J] {Q : ℕ}

/-- Treat the exterior row and column of a split array as new background
coordinates, fixing their sites. The fresh mark replaces the old one. -/
def child {H : Type} [Fintype H] (N : WireNode K J Q)
    (S : (∀ i, N.A i) → Fin Q → H → H → K)
    (hS : (split N.A (Fin Q) H S).coeff ≠ 0) (a b : J) (loss : ℝ) :
    WireNode K J Q := by
  let W := split N.A (Fin Q) H S
  let m : N.I ⊕ Fin 3 := .inr 0
  let σ := placeSplit N.site a a b
  let A' := fun i : {i : N.I ⊕ Fin 3 // i ≠ m} => W.Leg i.1
  let S' := markCoeff W m
  refine { I := {i : N.I ⊕ Fin 3 // i ≠ m}, A := A', other := ⟨.inl N.other, by simp [m]⟩,
           site := σ ∘ Subtype.val, T := S', nonzero := ?_, offset := N.offset + loss }
  exact marked_ne_zero W m hS

theorem cost_child {H : Type} [Fintype H]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
    (N : WireNode K J Q) (S : (∀ i, N.A i) → Fin Q → H → H → K)
    (hS : (split N.A (Fin Q) H S).coeff ≠ 0) (a b : J) (loss : ℝ) (p v : J) :
    cost φ c (N.child S hS a b loss) p v =
      rawLogPrice φ c ((split N.A (Fin Q) H S).group
        (placeSplit (Function.update N.site N.other v) p a b)) - (N.offset + loss) := by
  classical
  let W := split N.A (Fin Q) H S
  let m : N.I ⊕ Fin 3 := .inr 0
  let σ := placeSplit (Function.update N.site N.other v) p a b
  have hp : Function.update σ m p = σ := by
    apply Function.update_eq_self_iff.mpr
    rfl
  have h := rawLogPrice_update_eq_mark φ c W m σ p
  rw [hp] at h
  unfold cost
  apply congrArg (· - (N.offset + loss))
  refine Eq.trans ?_ h.symm
  apply congrArg (fun s => rawLogPrice φ c ((marked _ _ (markCoeff W m)).group (placeMark s p)))
  let o : {i : N.I ⊕ Fin 3 // i ≠ m} := ⟨.inl N.other, by simp [m]⟩
  let : DecidableEq {i : N.I ⊕ Fin 3 // i ≠ m} := fun _ _ => Classical.propDecidable _
  change Function.update (placeSplit N.site a a b ∘ Subtype.val) o v = σ ∘ Subtype.val
  funext i
  rcases i with ⟨i | k, hi⟩
  · by_cases he : i = N.other
    · subst i
      change Function.update (placeSplit N.site a a b ∘ Subtype.val) o v o = Function.update N.site N.other v N.other
      simp
    · have hne : (⟨Sum.inl i, hi⟩ : {i : N.I ⊕ Fin 3 // i ≠ m}) ≠ o :=
        fun h => he (Sum.inl.inj (congrArg Subtype.val h))
      rw [Function.update_of_ne hne]
      exact (Function.update_of_ne he _ _).symm
  · have hne : (⟨Sum.inr k, hi⟩ : {i : N.I ⊕ Fin 3 // i ≠ m}) ≠ o := by
      intro h
      have hv := congrArg Subtype.val h
      cases hv
    rw [Function.update_of_ne hne]
    fin_cases k
    · exact (hi rfl).elim
    all_goals rfl

end WireNode
end SiteTensor.Relocation

end

end SpectralBooks
end LinearAlgebra
end OAI
