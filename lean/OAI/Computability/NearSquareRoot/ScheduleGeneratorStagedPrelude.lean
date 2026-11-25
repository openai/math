import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagedAttempt
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagingSerializeRowsStates
import OAI.Computability.NearSquareRoot.ScheduleStagingStartupRoute
import OAI.Computability.NearSquareRoot.ScheduleStagingWidth

/-! # Effective numerical rows of the routed public startup -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Staged
open CommonAlphabet IntegerMultiplication TM ChunkControl
noncomputable section

variable {I P : Type} [Fintype I] [DecidableEq I] [Finite P] (d : Driver)
    [DecidableEq (StagingControl.Letter d)]

abbrev preNum (P : Type) [Finite P] (k : ℕ) : Numbering (StagingStartup.PC k P) :=
  ((SerializeRows.states k).sum (num P)).sum (num (Option Uniform.FenceInit.Control))

theorem preSize : Computable fun k => (preNum P k).size :=
  Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp SerializeRows.size (Computable.const _))
    (Computable.const _)

theorem preStart : Computable fun k => ((preNum P k).equiv (StagingStartup.start k)).val :=
  SerializeRows.start

/-- All startup operations other than the varying split counter belong to fixed finite controls.
The rejected serialization state is identified by its literal code before sequencing. -/
theorem preRows (a : Numbering (StagingProtection.Cell d))
    (sr : EffectiveRows a Numbering.bool SerializeRows.states (StagingSerialize.rule d))
    (wd : Rule (StagingProtection.Cell d) P Bool) (ws : P) (sep : StagingControl.Letter d) :
    EffectiveRows a (tapeNum d I) (preNum P)
      (fun k => StagingStartup.prelude d k wd ws sep) := by
  let r := fun (_ k : ℕ) => decide (k=8)
  have hr : Computable₂ r := (Primrec.eq.decide.to_comp.comp Computable.snd (Computable.const 8)).to₂
  have rc (k) (s : StagingSerialize.Phase k) :
      r k ((SerializeRows.states k).equiv s).val = StagingStartup.rejected k s := by
    change decide (SerializeRows.rank s = 8) = _
    rw [← SerializeRows.rank_rejected k]
    have eqr : SerializeRows.rank s = SerializeRows.rank (.rejected : StagingSerialize.Phase k) ↔ s = .rejected :=
      Fin.val_inj.trans (SerializeRows.states k).equiv.injective.eq_iff
    simp only [eqr]
    cases s <;> rfl
  let stages := tapeNum d I
  have first := (EffectiveRows.reject sr StagingStartup.rejected r hr rc).route
    (Pipeline.inputRoute (StagingStartup.inputReg d)) stages
  have width := (EffectiveRows.constant a Numbering.bool (num P) wd).route
    (StagingStartup.publicRoute _) stages
  have mark := (EffectiveRows.constant a (num (StagingMarks.W d I)) (num (Option Uniform.FenceInit.Control))
    (StagingMarks.rule d sep)).route (StagingStartup.markRoute d) stages
  exact (first.seq width SerializeRows.size (fun _ => ws) (Computable.const _)).seq mark
    (Primrec.nat_add.to_comp.comp SerializeRows.size (Computable.const _)) (fun _ => none) (Computable.const _)

end
end Generator.Staged

end NearSquareRoot
end Computability
end OAI
