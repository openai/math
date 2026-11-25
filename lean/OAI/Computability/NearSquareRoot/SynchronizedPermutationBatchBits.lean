import OAI.Computability.NearSquareRoot.SynchronizedPermutationBatchSemantics

/-! # The literal bit action of one batched switch layer -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes

variable {E B : Type*} (which : B → ℕ) (w : B → ℕ) (t : E → B → RawTable)
  (a : Bool × ℕ) (batch : ℕ)

theorem batchStage_outer (x : PackedAddress E w) :
    (batchStage which w t a batch x).1 = x.1 := rfl

theorem batchStage_bit (x : PackedAddress E w) (b : B) (n : Fin (w b)) :
    (batchStage which w t a batch x).2 b n =
      let c := rawSetting (t x.1 b) a.2 (List.ofFn (x.2 b))
      if which b = batch ∧ a.2 = n.val then x.2 b n ^^ (if a.1 then c.2 else c.1)
      else x.2 b n := by
  by_cases h : which b = batch <;> simp [batchStage, controlledPerm, h, stagePerm_apply]

theorem batchStage_selfInverse : (batchStage which w t a batch).symm = batchStage which w t a batch := by
  apply Equiv.ext
  intro x
  apply Prod.ext
  · rfl
  funext b
  by_cases h : which b = batch <;> simp [batchStage, controlledPerm, h, stagePerm_selfInverse]

end Benes

end NearSquareRoot
end Computability
end OAI
