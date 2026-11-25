import OAI.Hierarchy.DescentChronologicalGrains
import OAI.Hierarchy.DescentRecordedPeriod

namespace OAI
/-! # Reading the reset at the end of an issued branch -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentColonies DescentKernelHistory
noncomputable section

universe v

variable {F P : Type} [Field F] {d k wire hist : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ}
  {I W : MarkedWorld F d P bits} {i₀ z₀ D₀ i z D : ℕ}
  {initial : Reached I G q ε S k i₀ z₀ D₀ wire hist}
  {current : Reached W G q ε S k i z D wire hist}

/-- The terminal instruction of a nonempty number of full epochs is a reset. -/
theorem kindCalendar_last {height : ℕ} (rounds : ℕ) (positive : 0<height) :
    (kindCalendar rounds height).getLast?=some true := by
  cases height with
  | zero=>omega
  | succ n=>simp [kindCalendar,List.replicate_succ',kindPeriod]

/-- Match the final instruction of this specific path. The result can depend on the
entire physical path, including its reached terminal world. The reset handler
receives both the recorded prefix and its recorded last step. -/
def Path.terminal_of_last_reset
    (path : Path initial current) (p : ℕ) (record : path.recorded p)
    (finished : path.kinds.getLast?=some true)
    (result : ∀{W' : MarkedWorld F d P bits} {i' z' D' : ℕ}
      {u : Reached W' G q ε S k i' z' D' wire hist}, Path initial u → Sort v)
    (atReset : ∀{W' : MarkedWorld F d P bits} {age grain degree n h C f g cut tail : ℕ}
      {src : Reached W' G q ε S k age grain degree wire hist}
      {rate : ResetRates G S k degree n h C f g cut tail}
      (before : Path initial src) (B : ClosedReset src rate),
      HEq path (before.reset B) → before.recorded p → B.Recorded p → result (before.reset B)) :
    result path := by
  cases path with
  | here=>simp [Path.kinds] at finished
  | ordinary before ticket=>simp [Path.kinds] at finished
  | reset before B=>exact atReset before B HEq.rfl record.1 record.2

end
end Hierarchy.DescentSixParty.Chronology

end OAI
