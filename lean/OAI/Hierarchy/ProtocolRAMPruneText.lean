import OAI.Hierarchy.ProtocolRAMPruneFlag
import OAI.Hierarchy.ProbeStageProgramSize

namespace OAI
/-! # Physical program text of the final signed score comparison -/
noncomputable section
namespace Hierarchy.ProtocolRAM
open ProbeStage.Native ThreeFlat.RAM DescriptorExpr
theorem SumScores.procedure_text (W out n bound : ℕ) (e : Expr) :
    text (SumScores.procedure W out n bound e)=87+4*e.work := by
  simp only [SumScores.procedure,text,PhysicalInputPhases.writing,Term.labels_eq,SumScores.step_binds]
  omega

theorem PruneFlag.program_text (W out n threshold code : ℕ) (ends metrics layers : Bank) :
    text (SumScores.procedure W out n threshold (PruneFlag.term ends metrics layers code))=
      87+4*(47+20*code+9*code*(code+1)) := by
  rw [SumScores.procedure_text,PruneFlag.term_work]
end Hierarchy.ProtocolRAM


end

end OAI
