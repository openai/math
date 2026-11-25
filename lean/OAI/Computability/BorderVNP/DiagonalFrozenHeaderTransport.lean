import OAI.Computability.BorderVNP.DiagonalBootedProfilePublication

/-! # Transporting a published profile to its emitted header -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots GeometryAdvice
open Packing RoutingOutputs Crossing CellMacro.Generator RoutingISA.CompactMachine

/-- The profile paths and their pin publication survive the identification of the parsed
header with its emitted spelling, on the same hardware, memories and clocks. -/
theorem published_return_at_header {D p w d g o : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {task : SignedTaskArena.Layout} {dir : Directory.Layout} {N : Network D P bits}
    {cell : N.Site → Fin task.cube.cells} {edgeID : N.Edge ↪ Fin task.cube.cables} {portID : P ↪ Fin p}
    {original : Fin dir.entries → N.Site} {live : (Fin dir.teams × Fin dir.sites) ↪ P}
    {a : StartupArena} {u : Fin a.teams} {slot : ℕ} {packet : ReferencePacket w d} {origin gap : ℕ}
    {f : BroadcastFrame} {adv : AdviceLayout} {fields : Pins.ProcessorFields (a.operands u slot packet).layout}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {v : Fin g → Bool}
    {bank postPin preRegs : Bank w} {initial pinMem prePlace : Memory w} {time dest usedPin profCost : ℕ}
    {words : Fin o → ℕ} {old new : List Bool} (same : old = new)
    (paths : ProfilePaths (withStartup pinGeometry) g pub mac bank initial True time dest words
      (BootResidence (F := fields) a u slot packet f adv pub mac old initial bank))
    (published : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f old fields
      pub mac v postPin pinMem preRegs prePlace usedPin profCost) :
    ProfilePaths (withStartup pinGeometry) g pub mac bank initial True time dest words
      (BootResidence (F := fields) a u slot packet f adv pub mac new initial bank) ∧
    PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f new fields
      pub mac v postPin pinMem preRegs prePlace usedPin profCost := by
  cases same
  exact ⟨paths, published⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
