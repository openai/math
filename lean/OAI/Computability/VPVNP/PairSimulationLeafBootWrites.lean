import OAI.Computability.VPVNP.PairSimulationLeafBootRows
import OAI.Computability.VPVNP.PairSimulationLeafIncidentFootprint
import OAI.Computability.VPVNP.PairSimulationLeafScalarWrites

/-! # Register destinations of the complete virtual leaf bootstrap -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafBoot

open BurstRAM PrivateRAM RegisterOperands LeafStartup

variable {W p r k : ℕ}

/-- Every scalar, capacity and incident initialization row writes only its
declared operand bank. This covers rows reached by arbitrary physical data. -/
theorem destination_mem (pc : Label → Fin p) (reg : Reg ↪ Fin r) (nPub : Fin k) (done : Fin p)
    (j : Label) (a : Fin r) (h : destination (instruction (w := W) pc reg nPub done j) = some a) :
    a ∈ Set.range reg := by
  cases j with
  | pre i => fin_cases i <;> exact ⟨_,Option.some.inj h⟩
  | read i => exact ⟨_,Option.some.inj h⟩
  | increment i => exact ⟨_,Option.some.inj h⟩
  | capacity i => fin_cases i <;> exact ⟨_,Option.some.inj h⟩
  | scalar j =>
    obtain ⟨i,hi⟩ := LeafPortTable.destination_mem field (pc ∘ Label.scalar) (scalar reg)
      (pc (.incident (.inl 0))) scalarRows j a h
    exact ⟨.inl i,hi⟩
  | incident i =>
    obtain ⟨j,hj⟩ := LeafIncidentMachine.destination_mem (pc ∘ Label.incident) (geometry reg) done i a h
    exact ⟨geometryName j,hj⟩

end PairSimulation.LeafBoot

end VPVNP
end Computability
end OAI
