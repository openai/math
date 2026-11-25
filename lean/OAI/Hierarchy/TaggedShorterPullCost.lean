import OAI.Hierarchy.TaggedRadixPins

namespace OAI
/-! # Physical cell count of reindexed pins -/

namespace Hierarchy.Tagged.RadixStage
open ThreeFlat
@[simp] theorem pullPins_cells {F : Type*} {P Q : Type} [Fintype P] [Fintype Q]
    (N : BitNetwork F (Fintype.card P)) (wire : P → Q ⊕ Bool) :
    (pullPins N wire).cells=N.cells := by simp [pullPins,BitNetwork.glue_cells]
end Hierarchy.Tagged.RadixStage

end OAI
