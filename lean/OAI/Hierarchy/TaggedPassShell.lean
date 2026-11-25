import OAI.Hierarchy.TaggedRadixStaticNetwork
import OAI.Hierarchy.TaggedPassInputs
import OAI.Hierarchy.TaggedParallelStages
import OAI.Hierarchy.TaggedSortShell
import OAI.Hierarchy.TaggedAlignRows

namespace OAI
/-! # Port-level layout of one packed digit pass

Two equal-height local banks sort and align independently in their blocks.
The wide call stably orders contiguous packs by the key of the first lane.
Each rectangular adapter includes its dyadic padding and its fixed truncation.
-/

namespace Hierarchy.Tagged.Radix
open ThreeFlat Routing SortNetwork RadixStage
open scoped Classical
noncomputable section

namespace PassShape

/-- The entire pass uses exactly three tag occurrences when a product of
independent block switches is treated as one multilinear occurrence. -/
def network (F : Type*) [Zero F] [One F] (s : PassShape) {w : ℕ}
    (dummy : Fin w → Bool) (isReal isDummy : Fin w) (digit : Fin s.digitBits → Fin w) :
    Network F (RowBits s.rows w) (RowBits s.nextRows w) (s.PassHoles w) :=
  let localSort : Network F (s.LocalData w) (s.LocalData w) (Fin (s.sourceArity w)) :=
    parallel (fun _ : Fin s.blocks => SortRelation.shell (h := s.localBits) F (maskedDigit digit isDummy))
  let localAlign : Network F (s.LocalData w) (s.LocalData w) (Fin (s.alignArity w)) :=
    parallel (fun _ : Fin s.blocks => AlignShell.shell
      (AlignRows.network (j := s.packBits) (t := s.upperBits) F isReal digit))
  let globalSort : Network F (s.WideData w) (s.WideData w) (Fin (s.wideArity w)) :=
    SortRelation.shell F (s.wideDigit digit isDummy)
  seq (seq (seq (seq (seq (scatterNetwork F (s.enter dummy)) localSort) localAlign)
    (scatterNetwork F (s.wideInput dummy))) globalSort) (scatterNetwork F s.leave)

end PassShape
end
end Hierarchy.Tagged.Radix

end OAI
