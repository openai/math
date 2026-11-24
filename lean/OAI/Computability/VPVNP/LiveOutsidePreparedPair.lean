import OAI.Computability.VPVNP.LiveOutsidePairStages
import OAI.Computability.VPVNP.LiveProgramPairPreparation

/-! # Outside resource bounds of a physically prepared first-half group -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.OutsideBudget

open BurstRAM PrimedInputRAM LiveAuxiliaryHeaders PairStages.Group PairStages.Group.Auxiliary

/-- The three non-compression preparation logs in the first-half chronology
satisfy their resource bounds on the actual memories, histogram and pair
header. The workspace fit supplies all descriptor and copy separations. -/
theorem prepared_resources (G : PairStages.Group) (i : Fin (2^(sizes G).h)) (F : Nominations.Fits G)
    (m : Memory G.w) (tag : G.tagged Stage.nominations m) (μ : Nominations.Nom G)
    {hdr : Header (pairLengths G i) → Bool}
    (branch : PreparedBranch G m i hdr (Nominations.indexed G F m tag) μ)
    (fit : shadowBase G+span (pairLengths G i) (histLength G) ≤ 2^G.w)
    (clock : 68 ≤ G.clockAt Stage.auxiliaryCopy) :
    let t := G.constants.labels.eval G.g
    OutsideTraces.Resources ((Nominations.indexed G F m tag).logs μ) (4*(t+1)) 3 (5*(2*G.g.d)+23) ∧
    OutsideTraces.Resources (branch.init.logs ()) 100 26 92 ∧
    OutsideTraces.Resources (branch.copy.logs ()) (16*(auxWords (sizes G) t+1)) 15 115 := by
  have hlen : (histogram G μ).length = histLength G := by simp [histogram]
  have ht : (histogram G μ).length ≤ G.constants.labels.eval G.g := by
    rw [hlen]
    exact Nat.le_add_right (histLength G) G.constants.motifLabels
  have layout := geometry G i (histogram G μ).length hlen (hlen ▸ fit)
  exact ⟨nomination_resources G F m tag μ,
    initializer_logs_resources G i hlen layout.areas branch.initInputs branch.init (),
    copy_logs_resources G i ht layout.areas branch.copyPrepared clock layout.tagShadow branch.copy ()⟩

end LiveProgram.OutsideBudget

end VPVNP
end Computability
end OAI
