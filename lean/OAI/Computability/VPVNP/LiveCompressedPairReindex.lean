import OAI.Computability.VPVNP.LiveCompressedPairCursorStartup
import OAI.Computability.VPVNP.LiveCompressedPairFrames
import OAI.Computability.VPVNP.LiveCompressedPairMemory

/-!
# Joining descriptor choices and per-terminal branch data in the real pair table

A descriptor choice fixes the online path and its memory. The terminal
interpretation of that choice supplies the native arc and vertex paths on
that memory. The two classifications and the checked eight-call bootstrap
give the physical path corresponding to an ordinal emission, including every
deterministic setup and scheduling call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair
open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.Schedule LiveStageLink
open PairStages.Group.CompressedPaths

variable {d initial phases : ℕ} {C : Catalog d} (b : Bootstrap) (plan : Online.Config C initial phases)
variable (finalTable : PairTable) (G : PairStages.Group)
variable (B n base : ℕ) (m : Memory G.w)

local notation "operands" => publicWords G
local notation "clock" => fuel G
local notation "startup" => cursorStartupLogs b operands B n base m initial phases d
local notation "entry" => after m (eventLog startup)
local notation "onlinePath" => StagePaths b plan finalTable operands clock Stage.online entry

/-- The actual source-clock room required by the online transfer. -/
def originalOnlineEquiv :
    ActualPaths (original b plan finalTable operands Stage.online) (clockAt operands clock Stage.online) 0 entry
      (fun rs => ∀ r ∈ rs, room next (PairTag.address operands) Stage.online (clockAt operands clock Stage.online) r)
        ≃ onlinePath :=
  Equiv.subtypeEquivRight fun bs => by
    simp only [source_segment b plan finalTable operands Stage.online]

/-- Instantiation of the genuine source tables on one group's actual memory. -/
structure PhysicalStages where
  body : G.pair = pairTable b plan finalTable
  enough : 27 ≤ clock
  init : StartupResult b plan finalTable operands B n base m clock
  /-- The stage-tag protection established for the online calendar on the memory produced by
  startup. -/
  onlineFrame : Protected b plan finalTable operands clock Stage.online entry
  /-- The terminal-stage tag protection on the actual memory returned by each selected online
  path. -/
  terminalFrame : ∀ a : onlinePath, Protected b plan finalTable operands clock Stage.terminal (onlinePost a)

attribute [local irreducible] stages regs components

namespace PhysicalStages

variable {b plan finalTable G B n base m}
variable (S : PhysicalStages b plan finalTable G B n base m)

include S in
private theorem onlineTag : entry (PairTag.address operands).val = tagWord G.w Stage.online := by
  exact S.init.tagged

private def rawEquiv :
    ActualPaths (program b plan finalTable operands) clock 0 m (fun _ => True) ≃ Raw G m :=
  Equiv.subtypeEquivRight fun bs => by
    change _ ↔ ∃ rs, runSegment (G.pair.table.instantiate G.w operands).program clock (some 0) m bs = some rs ∧
      endState (some 0) rs = none ∧ True
    rw [S.body]

variable {Z I : Type*} {D : Z → Type*} (emit : (Σ z : Z, D z) ≃ I)
variable (descriptorPaths : Z ≃ StagePaths b plan finalTable (publicWords G) (fuel G) Stage.online
  (after m (eventLog (cursorStartupLogs b (publicWords G) B n base m initial phases d))))
variable (vertexPaths : ∀ z : Z, D z ≃ ActualPaths (original b plan finalTable (publicWords G) Stage.terminal)
  (clockAt (publicWords G) (fuel G) Stage.terminal) 0 (onlinePost (descriptorPaths z)) (fun _ => True))

include S emit descriptorPaths vertexPaths

/-- Reindex the semantic ordinal emission by every actual accepting path in
the compiled pair table. Both component correspondences are bidirectional. -/
noncomputable def reindex : I ≃ Raw G m :=
  emit.symm.trans ((Equiv.sigmaCongr (β₂ := fun a : onlinePath => ActualPaths (original b plan finalTable operands Stage.terminal)
      (clockAt operands clock Stage.terminal) 0 (onlinePost a) (fun _ => True)) descriptorPaths vertexPaths).trans
    ((fullEquiv b plan finalTable operands clock S.enough ((by decide : 10 ≤ 21).trans G.tagFit) m
      startup S.init.executed S.init.cursor S.onlineTag S.onlineFrame S.terminalFrame (fun _ => True)).trans S.rawEquiv))

theorem reindex_tape (z : Z) (x : D z) :
    (S.reindex emit descriptorPaths vertexPaths (emit ⟨z,x⟩)).val =
      List.replicate 8 [] ++ ((descriptorPaths z).val ++ (vertexPaths z x).val) := by
  simp only [reindex,Equiv.trans_apply,Equiv.symm_apply_apply,rawEquiv,Equiv.subtypeEquivRight_apply_coe,
    Equiv.sigmaCongr,Equiv.sigmaCongrRight_apply,Equiv.sigmaCongrLeft_apply,fullEquiv_tape]

/-- The actual reports at the handoff to the exponent checker, before the
outer linker adds its own tag dispatch and transfer events. -/
theorem reindex_logs (z : Z) (x : D z) :
    reports (S.reindex emit descriptorPaths vertexPaths (emit ⟨z,x⟩)) =
      startup ++ (onlineReports (descriptorPaths z) ++ (vertexPaths z x).property.choose.map (report operands Stage.terminal)) := by
  apply Option.some.inj
  have actual := rawRun (S.reindex emit descriptorPaths vertexPaths (emit ⟨z,x⟩))
  rw [reindex_tape] at actual
  have eq := congrArg (fun P : PairTable =>
    runSegment (P.table.instantiate G.w operands).program clock (some 0) m
      (List.replicate 8 [] ++ ((descriptorPaths z).val ++ (vertexPaths z x).val))) S.body
  exact actual.symm.trans (eq.trans (full_run b plan finalTable operands clock S.enough ((by decide : 10 ≤ 21).trans G.tagFit)
    m startup S.init.executed S.init.cursor S.onlineTag S.onlineFrame S.terminalFrame (descriptorPaths z) (vertexPaths z x).val
    (vertexPaths z x).property.choose (vertexPaths z x).property.choose_spec.1 (vertexPaths z x).property.choose_spec.2.1).1)

/-- The readback for dense exponents and preserved header cells is exactly
the final native terminal memory on the selected descriptor branch. -/
theorem reindex_after (z : Z) (x : D z) :
    after m (eventLog (reports (S.reindex emit descriptorPaths vertexPaths (emit ⟨z,x⟩)))) =
      after (onlinePost (descriptorPaths z)) (eventLog (vertexPaths z x).property.choose) := by
  rw [reindex_logs]
  exact joined_after m startup (descriptorPaths z) _


end PhysicalStages
end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
