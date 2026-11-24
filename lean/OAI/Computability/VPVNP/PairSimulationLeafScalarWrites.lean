import OAI.Computability.VPVNP.PairSimulationLeafPortTable
import OAI.Computability.VPVNP.PrivateRAMRegisterOperands

/-! # Register destinations of the scalar leaf startup -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafPortTable

open BurstRAM PrivateRAM RegisterOperands LeafStartup LeafRegisterBank

variable {K : Type} [DecidableEq K] {k p r w pubs : ℕ}

/-- Pointer allocation, field staging, and scalar filling write into the
register bank supplied by the enclosing leaf machine. -/
theorem destination_mem (field : K → Field k) (pc : Label K → Fin p) (reg : Reg K k ↪ Fin r)
    (done : Fin p) (rows : List K) (j : Label K) (a : Fin r)
    (h : destination (instruction (w := w) (pubs := pubs) field pc reg done rows j) = some a) :
    a ∈ Set.range reg := by
  cases j with
  | pointer port i | finish i | fill port i =>
    fin_cases i <;> first | exact ⟨_, Option.some.inj h⟩ | contradiction
  | stage port i =>
    simp only [instruction] at h
    split at h
    · rename_i hi
      generalize (Staging.code (scalarField (field port)))[i.val] = line at h
      obtain ⟨dst,rhs⟩ := line
      cases rhs <;> cases dst <;> exact ⟨_, Option.some.inj h⟩
    · contradiction

end PairSimulation.LeafPortTable

end VPVNP
end Computability
end OAI
