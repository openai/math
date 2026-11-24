import OAI.Computability.VPVNP.LiveProgramPairPreparation

/-! # The live counter array at entry to the compressed pair program -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary

open BurstRAM ChainAssignments CutSchedule LiveHeader LiveHeaderProgram

variable {G : Group} {m : Memory G.w} {i : Fin (2^(sizes G).h)} {hdr : PrimedInputRAM.Header (pairLengths G i) → Bool}
    {hw : 4 ≤ G.w} {advice : Bits (sizes G).advice} {cuts : AllCuts (sizes G).h (sizes G).delta}
    {mode : Mode.Tag} (out : Output (sizes G) (headerBase G) G.g.d hw advice cuts (halves (sizes G).h (.inl i)) mode m)
    (F : Nominations.Fits G) (tag : G.tagged Stage.nominations m) (μ : Nominations.Nom G)
    (P : PreparedBranch G m i hdr (Nominations.indexed G F m tag) μ) (hs : shadowBase G < 2^G.w)

include out hs

/-- The grammar prefix retains the nominated values, and every motif counter
starts at zero in the actual memory handed to the compressed computation. -/
theorem PreparedBranch.initialCounters :
    (∀ j : Fin (histLength G), (P.copy.memory () (counterBase G+j.val)).val = (μ j).val) ∧
    (∀ j : Fin G.constants.motifLabels, P.copy.memory () (counterBase G+histLength G+j.val) = 0) := by
  obtain ⟨h0,h1,h2,h3⟩ := geometry_order G
  obtain ⟨addr,_,base,_⟩ := address_values G hs
  have endFit := counter_end_le_shadow G
  change counterBase G + (histLength G + G.constants.motifLabels) ≤ shadowBase G at endFit
  have afterHeader : LiveHeaderSchedule.limit (sizes G) (headerBase G) ≤ (counter G).val := by
    change tableBase G ≤ (counter G).val
    omega
  have read (a : ℕ) (lo : counterBase G ≤ a) (hi : a < shadowBase G) :
      P.copy.memory () a = LiveNominations.stored (counter G) F.address μ m a := by
    rw [P.counterFrame _ lo hi,Nominations.memory_eq]
    exact ite_eq_right (by omega)
  constructor
  · intro j
    rw [read _ (by omega) (by have := j.isLt; omega),← base]
    exact LiveNominations.stored_at_val F.width_le _ _ _ _ _
  · intro j
    rw [read _ (by omega) (by have := j.isLt; omega)]
    exact (out.nomination_frame (counter G) F.address afterHeader μ).2 _ (by change (counter G).val+histLength G ≤ _; omega)

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
