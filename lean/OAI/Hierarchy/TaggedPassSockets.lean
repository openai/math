import OAI.Hierarchy.TaggedPassHoles
import OAI.Hierarchy.TaggedRadixFormats
import OAI.Hierarchy.TaggedPassFormat

namespace OAI
/-! # Identifying the three physical radix sockets with their oracle calls -/

namespace Hierarchy.Tagged.Radix.PassShape
open CatalystSubstitution RadixStage CorrectionFrame
open scoped Classical
noncomputable section

variable {F : Type*} [Field F] {k : ℕ}

private def dataFormat (s : PassShape) (w : ℕ) : PassFormat where
  first := s.localBits
  second := s.localBits
  wide := s.globalHeight
  copies := s.blocks
  firstW := s.localBits+w
  secondW := w
  wideW := s.globalHeight+s.pack*w

private def dataSocket (s : PassShape) (w : ℕ) (Y : (dataFormat s w).Calls F k) : s.PassHoles w ≃ Sockets Y.occurrences where
  toFun
    | .inl (.inl (.inl (.inl (.inr x)))) => .inl x
    | .inl (.inl (.inl (.inr x))) => .inr (.inl x)
    | .inl (.inr x) => .inr (.inr (.inl x))
    | .inl (.inl (.inl (.inl (.inl x)))) => nomatch x
    | .inl (.inl (.inr x)) => nomatch x
    | .inr x => nomatch x
  invFun
    | .inl x => .inl (.inl (.inl (.inl (.inr x))))
    | .inr (.inl x) => .inl (.inl (.inl (.inr x)))
    | .inr (.inr (.inl x)) => .inl (.inr x)
    | .inr (.inr (.inr x)) => nomatch x
  left_inv := by rintro (((((x|x)|x)|x)|x)|x) <;> first | rfl | exact nomatch x
  right_inv := by rintro (x|x|x|x) <;> first | rfl | exact nomatch x

private theorem attached_aux (s : PassShape) (w : ℕ) (g : PassFormat) (eq : g = dataFormat s w) (Y : g.Calls F k) :
    ∃ e : s.PassHoles w ≃ Sockets Y.occurrences, ∀ z,
      exactWeight Y.occurrences (z ∘ e.symm) = weight F s w z := by
  subst g
  refine ⟨dataSocket s w Y,?_⟩
  intro z
  simp only [PassFormat.Calls.occurrences,exactWeight,weight,pairWeight,one_mul,mul_one,mul_assoc]; rfl

theorem attached (s : PassShape) (w : ℕ) (room : s.packBits+2 ≤ s.digitBits) (Y : (s.format w).Calls F k) :
    ∃ e : s.PassHoles w ≃ Sockets Y.occurrences, ∀ z, exactWeight Y.occurrences (z ∘ e.symm) = weight F s w z := by
  have same : s.localBits = 2*s.digitBits+1 := by unfold localBits upperBits; omega
  exact attached_aux s w _ (by simp [format,dataFormat,same]) Y

end
end Hierarchy.Tagged.Radix.PassShape

end OAI
