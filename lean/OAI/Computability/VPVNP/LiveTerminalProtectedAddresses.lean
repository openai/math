import OAI.Computability.VPVNP.LiveCompressedPairStartupInputs
import OAI.Computability.VPVNP.LiveProgramCompressedPairPaths

/-!
# The live addresses protected by the compressed pair terminal traversal

The pair-level tag lies immediately after the dense counter array.
Every header or input address below the descriptor table precedes the
grammar counter array. Both ranges precede the final shared wire bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair
open BurstRAM PairStages.Group PairStages.Group.CompressedPaths

theorem terminal_protected_addresses (G : PairStages.Group) (lo : ℕ)
    (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w) (workspaceLow : ((publicWords G) 2).val ≤ lo) :
    let tag := (PairTag.address (publicWords G)).val
    (tag < lo ∧ Auxiliary.counterBase G+Auxiliary.histLength G+G.constants.motifLabels = tag) ∧
    ∀ a < Auxiliary.tableBase G, a < lo ∧ a < Auxiliary.counterBase G + Auxiliary.histLength G := by
  let c := G.constants
  let g := G.g
  let tag := (PairTag.address (publicWords G)).val
  have ws : ((publicWords G) 2).val = (Layout.pairWorkspace c).eval g := Nat.mod_eq_of_lt fit
  have ht := tag_before_workspace c g
  have exactTag : tag = (Layout.oldState c).eval g := by
    dsimp only [tag,publicWords]
    rw [tag_address]
    exact Nat.mod_eq_of_lt (ht.trans fit)
  have grammar : Auxiliary.counterBase G + Auxiliary.histLength G + G.constants.motifLabels = tag := by
    rw [exactTag]
    change _ + _ + _ = (Layout.counter c).eval g + (c.grammarLabels.eval g + c.motifLabels)
    exact Nat.add_assoc ..
  have tagLow : tag < lo := by rw [ws] at workspaceLow; exact exactTag.symm ▸ ht.trans_le workspaceLow
  have table := (Auxiliary.geometry_order G).2.2.1
  refine ⟨⟨tagLow,grammar⟩,?_⟩
  intro a ha
  exact ⟨by omega,by omega⟩

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
