import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Deterministic native phases interleaved with the chronological meter -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
/-- The external part of a date produces its actual next memory image. In an
ordinary date this includes the predecessor's packed signed donor column. -/
structure NativePhase (bw : ℕ) where
  program : Procedure bw
  ticks : ℕ
  image : Memory bw→Memory bw
  cheap : ProtocolRAM.CheapCode program

namespace NativePhase
variable {w : ℕ} (p q : NativePhase w)

/-- Execute two concrete source publishers in the same RAM. -/
def seq : NativePhase w :=
  ⟨p.program.seq q.program,p.ticks+q.ticks,fun m=>q.image (p.image m),ProtocolRAM.cheap_seq p.cheap q.cheap⟩

def Runs (m : Memory w) := p.program.Exec m (p.image m) p.ticks

theorem seq_runs (m : Memory w) (one : p.Runs m) (two : q.Runs (p.image m)) : (p.seq q).Runs m := by
  intro P R K mach pc reg pub exit rom advice cfg raw enter same
  exact Procedure.Exec.then one two mach pc reg pub exit rom advice cfg raw enter same

theorem seq_keeps (m : Memory w) (addr : ℕ) (one : p.image m addr=m addr)
    (two : q.image (p.image m) addr=p.image m addr) :
    (p.seq q).image m addr=m addr := two.trans one

end NativePhase
end Hierarchy.DescentSixParty.Chronology

end OAI
