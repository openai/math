import OAI.Hierarchy.DescentPrivateNativeReplay
import OAI.Hierarchy.DescentPrivateMeterAny

namespace OAI
/-! # The replayed program executes on arbitrary operands at every date -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k j i z₀ D₀ z D wire hist bw a : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist}

namespace MeterCalendar
variable {path : Path start source} (cal : MeterCalendar start a bw path)

/-- Static word room and totality of the two external geometry publishers,
independent of the input, validity, or equality of donor fields. -/
def Total (K : ℕ) : Prop := by
  induction cal with
  | seed=>exact a+1<2^bw
  | ordinary prev ticket port emit ih=>exact ih ∧ (∀m,emit.Runs m) ∧ MeterPort.Fits ticket port a bw K
  | reset prev closed emit ih=>exact ih ∧ ∀m,emit.Runs m

theorem any (K : ℕ) (total : cal.Total K) (m : Memory bw) :
    cal.program.Exec m (cal.memory m) cal.ticks ∧ ProtocolRAM.CheapCode cal.program := by
  refine ⟨?_,cal.cheap⟩
  induction cal with
  | seed=>exact DescentPrivateHeader.initialize_run a m total
  | ordinary prev ticket port emit ih=>
    obtain ⟨earlier,stage,room⟩:=total
    have first : prev.program.Exec m (prev.memory m) prev.ticks := ih earlier
    have second : emit.Runs (prev.memory m) := stage (prev.memory m)
    have third : (MeterPort.program ticket port a bw).Exec (emit.image (prev.memory m))
        (MeterPort.image ticket port a (emit.image (prev.memory m))) (MeterPort.ticks ticket port a) :=
      MeterPort.any ticket port a K (emit.image (prev.memory m)) room
    intro P₀ R K₀ mach pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then (Procedure.Exec.then first second) third mach pc reg pub exit rom advice cfg raw enter same
  | reset prev reset emit ih=>
    obtain ⟨earlier,stage⟩:=total
    intro P₀ R K₀ mach pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then (ih earlier) (stage (prev.memory m)) mach pc reg pub exit rom advice cfg raw enter same

end MeterCalendar
end
end Hierarchy.DescentSixParty.Chronology

end OAI
