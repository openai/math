import OAI.Computability.VPVNP.FixedPaperDescriptorPasses
import OAI.Computability.VPVNP.FixedPaperActualRows

/-! # The complete fixed native compressed-pair compiler

The template, parameter numbering, descriptor script, local vertex program,
and address multiplier are fixed before the exceptional length. Every
sufficiently large length then supports all finite models and all nominated
groups of this single physical program.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program
open Compression CursorNetwork LiveProgram CompressedPair CompressorRecords.ScheduledTrace
open PairSimulation

/-- One fixed pair table and address multiplier work for all sufficiently large
lengths and all finite-algebra models used by the diagonal argument. -/
theorem paperPairCompiler {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) (C : ℕ) :
    PairCompiler B C := by
  intro c hC labels _ N
  subst C
  let u := pairExponents B
  let addr := max N (max S.laneBits 5)
  have enough : max S.laneBits 5 ≤ addr := le_max_right ..
  have positive : 1 ≤ addr := (by decide : 1 ≤ 5).trans ((le_max_right ..).trans enough)
  let E := CompressorReader.program
  let raw := descriptorRate B
  let scan := VertexImage.RatedRoles.scan B (entryOrdinal B c labels)
  refine ⟨addr,le_max_left ..,positive,paperTable B u c labels,?_⟩
  apply eventually_pairRuns_of_nativeStages B u c labels E addr positive c.circuitExponent rfl raw enough
  · exact eventually_paperPasses B u c labels E addr positive c.circuitExponent
  · apply eventually_paperTerminals_of_rated B u c labels E addr positive raw scan enough
    exact eventually_paperRatedRows B u c labels E addr positive raw enough

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
