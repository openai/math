import OAI.Hierarchy.DescentTerminalLastProgram
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Space and running time of the final cutoff, histogram and failure scan -/
namespace Hierarchy.DescentTerminalLast
open DescentCensusRAM DescentStaticWordColumn ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

variable {w slots choices : ℕ} (L : Tape) (S : Banks w slots choices)
variable (cut stop rows word : ℕ)

theorem trailing_names : names (program L S cut stop rows word)=567 :=by
  have indexed (addresses values n : ℕ) :
      names (ProtocolRAMIndexedWrite.scatter w addresses values n)=20 := rfl
  have weighted (src n : ℕ) : names (ProtocolRAMWeightedScatter.program w src n)=22 := rfl
  simp only [program, tally, DescentCensusRAM.add, issue, ProtocolRAMGeneratedWrite.program,
    names_seq, names_scan, indexed, weighted, clipped, stopBit, safeKey, atZero,
    DescentCensusRAM.slot, Expr.work]

theorem trailing_invoice :
    ticks L S rows word+7*names (program L S cut stop rows word)≤4169+100*rows+6*choices+300*slots :=by
  rw [trailing_names]
  have clock:=bounded_clock L S rows word
  omega

end
end Hierarchy.DescentTerminalLast

end OAI
