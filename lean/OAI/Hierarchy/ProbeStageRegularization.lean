import OAI.Hierarchy.ProbeStagePhysicalOrdinal
import OAI.Hierarchy.ProbeStageReadback
import OAI.Hierarchy.ProbeStageProgramSize
import OAI.Hierarchy.ProbeSubdivision

namespace OAI
/-! # Native bounded-congestion subdivision of a permutation

The instruction stream, initial advice and stage addresses are fixed by
the format. The only variable input words are the supplied permutation
values. The output gives three permanent arrays at each move and preserves
the caller's entire higher-address data.
-/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

/-- All native address, coloring, rank, scatter, and mesh-geometry passes
execute on the same initial tape. The actual numbered moves are exactly
the moves in the injective payload route. -/
theorem execute_subdivision {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h)))
    (raw : Memory (wordBits h d copies)) (input : ∀ r : Fin (2^h),raw r.val=((π r).val : Word _)) :
    let start := inputTape h d _ raw
    let finish := images h d start (rounds d)
    (subdivisionProgram h d).Exec start finish (subdivisionConstant d*2^h) ∧
      (∀ (s : Fin (2*rounds d+1)) (c : Fin 3), Resident (stageBank h d s c) finish
        (fun r => fieldNumber (stageMatching π s) r c)) ∧
      (∀ s : Fin (2*rounds d+1), (advisedRoute h d π).layers[s.val]?=some (layer (stageMatching π s).tiles)) ∧
      (∀ x,heapEnd h d copies≤x → finish x=raw x) ∧
      text (subdivisionProgram h d)≤(53+15000*rounds d)*2^h := by
  obtain ⟨run,correct⟩ := native_linear_run hd π raw input (physical_ordinal hd π)
  exact ⟨run,fun s c => stageBank_reads π _ correct s c,stageMatching_route π,fun _ hx => images_above raw correct hx,
    subdivision_program_size ..⟩

end
end Hierarchy.ProbeStage.Native

end OAI
