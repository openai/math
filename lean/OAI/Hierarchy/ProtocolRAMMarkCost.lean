import OAI.Hierarchy.ProtocolRAMMarkLoad
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Constant instruction text and linear clock for native chain purchases -/

namespace Hierarchy.ProtocolRAM.MarkTape
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure

theorem cheap_cpu {w P R K : ℕ} (instr : Instr w P R K) (ok : markInstruction instr) :
    TaggedShorterCheapCPU.Cheap instr := by
  cases instr with
  | binary op a b c n => cases op <;> simp_all [markInstruction,TaggedShorterCheapCPU.Cheap]
  | _ => simp_all [markInstruction,TaggedShorterCheapCPU.Cheap]

theorem native_cheap (w tiles work first n base gates : ℕ) (marks : Bank) :
    CheapCode ((load w tiles work first n marks).seq (procedure w base gates)) := by
  have gatesSafe : CheapCode (procedure w base gates) := by
    intro P R K pc reg pub exit i
    exact cheap_cpu _ (cheap w base gates pc reg pub exit i)
  exact @cheap_seq w (load w tiles work first n marks) (procedure w base gates)
    (@scan_cheap w work (4+tiles+first+n) (loadTerm tiles marks)) (@gatesSafe)

theorem native_text (w tiles work first n base gates : ℕ) (marks : Bank) :
    let A := (load w tiles work first n marks).seq (procedure w base gates)
    A.labels=83 ∧ A.registers=30 ∧ A.slots=4 := by
  obtain ⟨labels,registers,slots⟩ := scan_size w work (4+tiles+first+n) (loadTerm tiles marks)
  have workCount : (loadTerm tiles marks).work=19 := rfl
  simp only [workCount] at labels registers
  refine ⟨?_,?_,?_⟩
  · change (scan w work (4+tiles+first+n) (loadTerm tiles marks)).labels + 19 = 83
    rw [labels]
  · change (scan w work (4+tiles+first+n) (loadTerm tiles marks)).registers + 7 = 30
    rw [registers]
  · change (scan w work (4+tiles+first+n) (loadTerm tiles marks)).slots + 4 = 4
    rw [slots]

/-- Each candidate path has fixed length H. The scratch initializer traverses one
word per tile or candidate. The addressed scan uses one bounded-time iteration per gate. -/
theorem native_clock (tiles first n H : ℕ) (marks : Bank) :
    loadClock tiles first n marks+(3+17*(n*(4*H+3))) =
      175+42*(tiles+first)+n*(93+68*H) := by
  change (4+(4+tiles+first+n)*(2*19+4))+(3+17*(n*(4*H+3)))=_
  ring

end Hierarchy.ProtocolRAM.MarkTape

end OAI
