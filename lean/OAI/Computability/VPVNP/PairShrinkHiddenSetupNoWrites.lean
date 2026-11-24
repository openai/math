import OAI.Computability.VPVNP.PairShrinkRolePhysicalHidden
import OAI.Computability.VPVNP.PairShrinkRoleMapStart
import OAI.Computability.VPVNP.CompressorFormulaFootprint

/-!
# External memory during shrinking setup

The hidden-field handoff runs locally and its compiled header only reads
external memory. Map entry likewise runs its four reload steps locally
and reads the four level fields and the packed site's count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation

open BurstRAM CompressorRecords
open scoped Fin.CommRing
open private eval_no_writes from OAI.Computability.VPVNP.CompressorFormulaFootprint
open private fetch from OAI.Computability.VPVNP.PairSimulationMapResidentInputs

variable {w endAddr : ℕ} (s t oldHead : ℕ) (m : Memory w) (level owner node : Word w)
    (saved : DFS.Scratch w endAddr)

theorem ShrinkRole.physicalHiddenSetup_noWrites :
    SourceTransport.Writes (fun _ ↦ False)
      ((ShrinkRole.physicalHiddenSetup s t oldHead m).trace node saved) := by
  intro a v h
  rcases List.mem_append.mp h with handoff | header
  · cases (List.mem_replicate.mp handoff).2
  · exact eval_no_writes (fun _ ↦ False) _ _ _ _ _ a v header

theorem ShrinkRole.after_physicalHiddenSetup :
    after m ((ShrinkRole.physicalHiddenSetup s t oldHead m).trace node saved) = m :=
  funext fun _ ↦ SourceTransport.after_outside m
    (physicalHiddenSetup_noWrites s t oldHead m node saved) id

theorem ShrinkVertexImage.mapStartSetup_noWrites :
    SourceTransport.Writes (fun _ ↦ False)
      ((ShrinkVertexImage.mapStartSetup m level owner).trace node saved) := by
  intro a v h
  change Event.write a v ∈ List.replicate 4 .tick ++ MapResidentInputs.headerEvents m level owner at h
  simp [MapResidentInputs.headerEvents, fetch] at h

theorem ShrinkVertexImage.after_mapStartSetup :
    after m ((ShrinkVertexImage.mapStartSetup m level owner).trace node saved) = m :=
  funext fun _ ↦ SourceTransport.after_outside m (mapStartSetup_noWrites m level owner node saved) id

end PairSimulation

end VPVNP
end Computability
end OAI
