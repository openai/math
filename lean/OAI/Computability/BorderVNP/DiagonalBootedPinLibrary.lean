import OAI.Computability.BorderVNP.DiagonalFrozenReturnInputs

/-! # The installed library of a returned native pin -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator RoutingISA.CompactMachine
open PackedHistoryCircuit BorderVNP.Cube CellMacro.Generator JointHeader Routing

variable {R r t d link inner n w : ℕ} {Edge : Type} {gen : Fragment IO}
    {G : Wiring R r t d link inner n Edge} {pub : Fin (R+1) → Arg → Word w}
    {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses} {pin : Fin d → Bool}
    {ext : Exterior R r link → Bool} {u : Fin (R+1)} (B : BootedPinStart gen G pub reg args pin ext u)

/-- The installed instruction routines are fixed before any guesses are read. -/
theorem BootedPinStart.start_routines :
    B.start.routines = TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n) := rfl

/-- Identify the installed library by its routines without expanding the instructions. -/
theorem BootedPinStart.installed_routines :
    install gen n B.start.routines = install gen n (TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n)) :=
  B.installed_routines_at.symm

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
