import OAI.Hierarchy.DescentPublicDateMachine
import OAI.Hierarchy.DescentPrivateCalendarAny

namespace OAI
/-! # One fixed program for all selected native histories, with the original meter -/
namespace Hierarchy.DescentSixParty.Chronology.MeterCalendar
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z₀ D₀ z D wire hist bw a : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k 0 z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist}
variable {path : Path start source} (cal : MeterCalendar start a bw path)

def publicAge (_ : MeterCalendar start a bw path) : ℕ := i

/-- Only the equality of actual opcode and tick components is compared. The reached
memory image, including the incoming topology, can differ for every selector value. -/
def Scheduled (date : ℕ→DateCode bw) : Prop := by
  induction cal with
  | seed=>exact True
  | ordinary prev ticket port emit ih=>
    exact ih ∧ date (publicAge prev)=.ordinary emit.program emit.ticks (MeterPort.program ticket port a bw)
      (MeterPort.ticks ticket port a)
  | reset prev closed emit ih=>exact ih ∧ date (publicAge prev)=.reset emit.program emit.ticks

theorem public_code (date : ℕ→DateCode bw) (issued : cal.Scheduled date) :
    cal.program=DateCode.compile a date i ∧ cal.ticks=DateCode.clock date i := by
  induction cal with
  | seed=>exact ⟨rfl,rfl⟩
  | ordinary prev ticket port emit ih=>
    obtain ⟨past,last⟩:=issued
    dsimp only [publicAge] at last
    obtain ⟨code,time⟩:=ih past
    refine ⟨?_,?_⟩
    · change (prev.program.seq emit.program).seq (MeterPort.program ticket port a bw)=_
      rw [DateCode.compile,last,DateCode.extend,code]
    · change (prev.ticks+emit.ticks)+MeterPort.ticks ticket port a=_
      rw [DateCode.clock,last,DateCode.ticks,time,Nat.add_assoc]
  | reset prev closed emit ih=>
    obtain ⟨past,last⟩:=issued
    dsimp only [publicAge] at last
    obtain ⟨code,time⟩:=ih past
    refine ⟨?_,?_⟩
    · change prev.program.seq emit.program=_
      rw [DateCode.compile,last,DateCode.extend,code]
    · change prev.ticks+emit.ticks=_
      rw [DateCode.clock,last,DateCode.ticks,time]

theorem published (date : ℕ→DateCode bw) (issued : cal.Scheduled date) (K : ℕ)
    (total : cal.Total K) (m : Memory bw) :
    (DateCode.compile a date i).Exec m (cal.memory m) (DateCode.clock date i) ∧
      ProtocolRAM.CheapCode (DateCode.compile a date i) := by
  have eqn:=cal.public_code date issued
  rw [←eqn.1,←eqn.2]
  exact cal.any K total m

/-- Opcode labels, register names, and public clock of the actual chronological CPU
are paid for by exactly the same list of public date invoices. -/
theorem paid (date : ℕ→DateCode bw) (issued : cal.Scheduled date) :
    (cal.ticks+7*DescentStaticWordColumn.names cal.program)*bw=
      115*bw+∑j∈Finset.range i,(date j).tariff := by
  obtain ⟨code,time⟩:=cal.public_code date issued
  rw [code,time,DateCode.billing]

end
end Hierarchy.DescentSixParty.Chronology.MeterCalendar

end OAI
