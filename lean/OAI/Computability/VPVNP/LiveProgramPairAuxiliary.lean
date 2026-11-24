import OAI.Computability.VPVNP.LiveProgramPairStages
import OAI.Computability.VPVNP.PairedChain

/-! # The public operands of the two sparse-header preparation stages -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary
open BurstRAM PrimedInputRAM LiveAuxiliaryHeaders
open scoped Fin.CommRing

variable (G : Group)

/-- Live header sizes obtained by evaluating the fixed length expressions at the group
geometry. -/
abbrev sizes := G.constants.lengths.eval G.g
/-- Auxiliary input-field lengths for the chosen first-half pair, determined by its index and
the live chain, cut, and advice sizes. -/
abbrev pairLengths (i : Fin (2^(sizes G).h)) :=
  PairedChain.lengths (sizes G).h (sizes G).delta (sizes G).advice i

/-- Descriptor table’s base address encoded at the RAM word width. -/
abbrev desc := Pieces.word G.g G.lit (.geometry (Layout.descriptor G.constants))
/-- Virtual shadow’s base address encoded at the RAM word width. -/
abbrev shadow := Pieces.word G.g G.lit (.geometry (Layout.shadow G.constants))
/-- Label-counter array’s base address encoded at the RAM word width. -/
abbrev counter := Pieces.word G.g G.lit (.geometry (Layout.counter G.constants))

/-- The seven physical source addresses from which the auxiliary header copy reads its fields
and nominated counts. -/
abbrev source := LiveAuxiliaryStages.headerSources (sizes G) (Layout.header.eval G.g) (counter G)

/-- Every public operand of the initializer agrees with the concrete sparse
header geometry, including its array of seven physical source addresses. -/
theorem init_data (i : Fin (2^(sizes G).h)) (hist : List (Word G.w))
    (hlen : hist.length = G.constants.grammarLabels.eval G.g) :
    Pieces.word G.g G.lit ∘ InputOperand.geometry ∘ StageOperands.auxiliary G.constants =
      initData (pairLengths G i) hist.length (shadow G) (desc G) (source G) := by
  rw [hlen]
  funext j
  fin_cases j <;> rfl

/-- The guarded copy reads its end cursor from the final descriptor. -/
theorem copy_data :
    Pieces.word G.g G.lit ∘ InputOperand.geometry ∘ StageOperands.auxiliaryCopy G.constants =
      LiveAuxiliaryStages.copyData (desc G) := by
  funext j
  fin_cases j
  · rfl
  · rw [LiveAuxiliaryStages.copyData]
    change Fin.ofNat _ ((Layout.descriptor G.constants).eval G.g + 18) =
      LiveHeaderCopyDispatch.address (desc G) 6 0
    rw [LiveAuxiliaryStages.copy_endAddress]
    exact Nat.cast_add (R := Word G.w) _ _

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
