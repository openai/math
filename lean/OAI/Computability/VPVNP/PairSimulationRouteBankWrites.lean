import OAI.Computability.VPVNP.PairSimulationRouteBank
import OAI.Computability.VPVNP.PrivateRAMRegisterOperands

/-! # Register destinations in the complete cursor routing scan -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteBank

open BurstRAM PrivateRAM RouteSchedule RegisterOperands
open private callText from OAI.Computability.VPVNP.PairSimulationRouteBank
open private RouteGeometry.row from OAI.Computability.VPVNP.PairSimulationRouteGeometry

variable {p r k : ℕ}

private theorem call_destination_mem (labels : CallLabels p) (reg : Fin 32 ↪ Fin r)
    (done : Fin p) (j : Call) (a : Fin r)
    (h : destination (callText (k := k) labels reg done j) = some a) : a ∈ Set.range reg := by
  rcases j with i | i | i
  · simp only [callText, RouteGeometry.instruction] at h
    cases eqn : (RouteGeometry.row i).2 <;> rw [eqn] at h <;> exact ⟨_, Option.some.inj h⟩
  · fin_cases i <;> first | exact ⟨_, Option.some.inj h⟩ | contradiction
  · fin_cases i <;> first | exact ⟨_, Option.some.inj h⟩ | contradiction

/-- Each write in the scheduler, its loops, or either field call targets one
of the 32 registers in the relocated routing bank. -/
theorem destination_mem (loc : Address → Fin p) (reg : Fin 32 ↪ Fin r) (j : Address) (a : Fin r)
    (h : destination (text (k := k) loc reg j) = some a) : a ∈ Set.range reg := by
  rcases j with (control | sCall | lCall) | exit
  · rcases control with i | i | i | i <;> fin_cases i <;>
      first | exact ⟨_, Option.some.inj h⟩ | contradiction
  · exact call_destination_mem _ reg _ sCall a h
  · exact call_destination_mem _ reg _ lCall a h
  · fin_cases exit <;> contradiction

end PairSimulation.RouteBank

end VPVNP
end Computability
end OAI
