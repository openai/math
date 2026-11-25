import OAI.LinearAlgebra.FiniteFourier.PrimeTemplateProgram.PrimeRoutedProgram
import Mathlib.Data.Fintype.Option

/-! # Independent prime-kernel programs on a finite family of rectangular blocks -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace PrimeTemplateProgram

variable {K : Type*} [CommSemiring K] {ℓ f F : ℕ} {ζ : K}

private def splitLast (B X : Type) : X × Option B ≃ X ⊕ (X × B) where
  toFun
    | (x, none) => .inl x
    | (x, some b) => .inr (x, b)
  invFun
    | .inl x => (x, none)
    | .inr (x,b) => (x, some b)
  left_inv := by rintro ⟨x, _ | b⟩ <;> rfl
  right_inv := by rintro (x | ⟨x,b⟩) <;> rfl

/-- Realize all the blocks independently. Rectangular blocks may have
different programs, and both budgets add exactly across the block family. -/
theorem blockDiagonal {L I O : Type} [Fintype L] [DecidableEq L] [Fintype I] [Fintype O]
    {A : L → Matrix O I K} {c s : L → ℕ}
    (p : ∀ l, PrimeTemplateProgram ℓ f F ζ (A l) (c l) (s l)) :
    PrimeTemplateProgram ℓ f F ζ (Matrix.blockDiagonal A) (∑ l, c l) (∑ l, s l) := by
  classical
  let P (B : Type) [Fintype B] := ∀ [DecidableEq B] (A : B → Matrix O I K) (c s : B → ℕ),
    (∀ b, PrimeTemplateProgram ℓ f F ζ (A b) (c b) (s b)) →
      PrimeTemplateProgram ℓ f F ζ (Matrix.blockDiagonal A) (∑ b, c b) (∑ b, s b)
  have h : P L := by
    apply Fintype.induction_empty_option (P := P)
    · intro B D inst e ih
      let _ : Fintype B := Fintype.ofEquiv D e.symm
      intro _ A c s p
      have h₁ := ih (A ∘ e) (c ∘ e) (s ∘ e) (fun b => p (e b))
      have h₂ := h₁.reindex (Equiv.prodCongr (Equiv.refl O) e) (Equiv.prodCongr (Equiv.refl I) e)
      convert h₂ using 1
      · ext ⟨o,d₁⟩ ⟨i,d₂⟩
        simp [Matrix.reindex_apply, Matrix.blockDiagonal_apply]
      · exact (e.sum_comp c).symm
      · exact (e.sum_comp s).symm
    · intro _ A c s _
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact localCircuit ⟨0, le_rfl, ⟨.nil, fun _ => .zero⟩, by ext ⟨_, b⟩; exact b.elim⟩
    · intro B inst ih _ A c s p
      have h₁ := ih (A ∘ some) (c ∘ some) (s ∘ some) (fun b => p (some b))
      have h₂ := ((p none).fromBlocks h₁).reindex (splitLast B O).symm (splitLast B I).symm
      convert h₂ using 1
      · ext ⟨o, _ | b₁⟩ ⟨i, _ | b₂⟩ <;>
          simp [Matrix.reindex_apply, Matrix.blockDiagonal_apply, splitLast]
      · exact Fintype.sum_option c
      · exact Fintype.sum_option s
  exact h A c s p

end PrimeTemplateProgram

end FiniteFourier
end LinearAlgebra
end OAI
