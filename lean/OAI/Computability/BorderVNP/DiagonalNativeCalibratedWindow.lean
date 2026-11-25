import OAI.Computability.BorderVNP.DiagonalNativePhysicalWindow
import OAI.Computability.BorderVNP.RoutingISAScheduleClockPhases

/-! # Residual clock from the calibrated §11 evaluator allowance -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction CompactMachine CellMacro.Generator
open BorderVNP.Cube BorderVNP.Cube.Tally ScheduleClock

variable {dim box lanes selectors symbols w k : ℕ}
variable (id : TableEntry dim box lanes selectors symbols → ℕ)
variable (pub : Arg → Word w) (routines : TeamOpcode.Macros w 8) (gen : Fragment IO) (n : ℕ)
variable (s : Bank w) (m : Memory w)
variable (pins : (Fin k → Bool) ≃ Pins.Return pub (install gen n routines) s m)

/-- Use the physical complete allowance, with independent pre- and post-call cube charges.
The remaining arguments are the measured return bounds of the five native phases, at their
actual chronological boundaries. The resulting window feeds the signed product at the
processor's true residual clock. -/
def SignedStageWindow.ofPhaseAllowance
    (used limit core geometry fixed R V entries cells bundles desc decl cables cubeUnits F H
      publicWords powers exterior rectangle reader : ℕ)
    (bound : completeAllowance core geometry fixed R V entries cells bundles desc decl cables cubeUnits
      (2*F) H w publicWords powers exterior (rectangle+reader) ≤ limit) :=
  let c := phaseCharges core geometry fixed R V entries cells bundles desc decl cables cubeUnits F H w
    publicWords powers exterior rectangle reader
  SignedStageWindow.ofCharges id pub routines gen n s m pins used limit c.core c.before c.argumentsCalls c.finish c.reader
    ((sum_le_completeAllowance core geometry fixed R V entries cells bundles desc decl cables cubeUnits F H w
      publicWords powers exterior rectangle reader).trans bound)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
