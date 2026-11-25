import OAI.Hierarchy.DescentTerminalSlotsNames
import OAI.Hierarchy.DescentTerminalMeterPrice
import OAI.Hierarchy.DescentTerminalPlacedClock
import OAI.Hierarchy.DescentTerminalChipRuntime

namespace OAI
/-! # Literal instruction count for the placed terminal rows and final five scans -/
namespace Hierarchy
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentStaticWordColumn DescentTerminalVertexFields

theorem DescentTerminalProposalCheck.names (w out n:ℕ) (a b:Bank) :
    DescentStaticWordColumn.names (DescentTerminalProposalCheck.program w out n a b)=155 := by
  have c : (DescentTerminalProposalCheck.compare a b).work=17:=rfl
  simp only [DescentStaticWordColumn.names,DescentTerminalProposalCheck.program,SumScores.procedure,
    PhysicalInputPhases.writing,DescriptorExpr.Term.labels_eq,SumScores.step_binds,c]

theorem DescentTerminalChipRuntime.program_names (A:DescentTerminalChipRuntime.Layout)
    (L:DescentTerminalChipRuntime.Banks) (w N slots:ℕ) :
    names (DescentTerminalChipRuntime.program A L w N slots)=787 := by
  have fixed₁ : (DescentTerminalChipRuntime.dense L).work=50:=rfl
  have fixed₂ : (DescentTerminalChipRuntime.route L).work=31:=rfl
  have fixed₃ : (DescentTerminalChipRuntime.key L).work=30:=rfl
  simp only [DescentTerminalChipRuntime.program,names_seq,names_scan,DescentTerminalProposalCheck.names,fixed₁,fixed₂,fixed₃]

namespace DescentTerminalCompiledPrefix
theorem Suffix.names (S:Shape) (L:Layout) {blocks:ℕ} (F:MaskedShelf blocks) (w:ℕ) :
    DescentStaticWordColumn.names (Suffix.program (w:=w) S L F)=
       2273+468*blocks+DescentStaticWordColumn.names (DescentTerminalEmitter.program (w:=w) S.terminal L.emit) := by
  unfold Suffix.program
  rw [names_seq,names_seq,Suffix.slots_names,names_seq,names_scan,names_scan,masked_work,gather_cost]
  omega

end DescentTerminalCompiledPrefix
end Hierarchy

end OAI
