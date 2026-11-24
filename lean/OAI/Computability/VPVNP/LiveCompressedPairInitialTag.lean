import OAI.Computability.VPVNP.LiveProgramPairPreparation
import OAI.Computability.VPVNP.LiveProgramCompressedPair

/-!
# The compressed pair starts in its row-count stage

The linker uses the first old-state word, immediately after the grammar and
motif counters. The header's zero suffix covers this cell. The nomination,
auxiliary initialization and shadow-copy calls preserve it through pair entry.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary

open BurstRAM ChainAssignments CutSchedule LiveHeader LiveHeaderProgram

variable {G : Group} {m : Memory G.w} {i : Fin (2^(sizes G).h)}
  {hdr : PrimedInputRAM.Header (pairLengths G i) → Bool} {hw : 4 ≤ G.w}
  {advice : Bits (sizes G).advice} {cuts : AllCuts (sizes G).h (sizes G).delta} {mode : Mode.Tag}

theorem PreparedBranch.startup_tag
    (out : Output (sizes G) (headerBase G) G.g.d hw advice cuts (halves (sizes G).h (.inl i)) mode m)
    (F : Nominations.Fits G) (tag : G.tagged Stage.nominations m) (μ : Nominations.Nom G)
    (P : PreparedBranch G m i hdr (Nominations.indexed G F m tag) μ) (hs : shadowBase G < 2^G.w) :
    let pub := Pieces.word G.g G.lit ∘ StageOperands.pair G.constants
    P.copy.memory () (PairTag.address pub).val = 0 := by
  intro pub
  let cell := (Layout.oldState G.constants).eval G.g
  have hi : cell < shadowBase G := by
    change cell < ((((((cell + G.constants.configWords.eval G.g) + G.constants.configWords.eval G.g) + 5) + 24)
      + G.constants.prefixCapacity.eval G.g) + G.constants.labels.eval G.g)
    omega
  have lo : counterBase G + histLength G ≤ cell := by
    change counterBase G + histLength G ≤ counterBase G + (histLength G + G.constants.motifLabels)
    omega
  have atCell : (PairTag.address pub).val = cell := by
    rw [CompressedPair.tag_address G.constants G.g G.lit]
    exact Nat.mod_eq_of_lt (hi.trans hs)
  obtain ⟨h0,h1,h2,_⟩ := geometry_order G
  obtain ⟨addr,_,base,_⟩ := address_values G hs
  have hheader : LiveHeaderSchedule.limit (sizes G) (headerBase G) ≤ (counter G).val := by
    change tableBase G ≤ (counter G).val
    omega
  rw [atCell, P.counterFrame cell (by omega) hi, Nominations.memory_eq]
  simp only [LiveStageLink.transferMemory, writeMemory, ite_eq_right (by omega : cell ≠ G.addr.val)]
  exact (out.nomination_frame (counter G) F.address hheader μ).2 cell
    (by change (counter G).val+histLength G ≤ cell; omega)

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
