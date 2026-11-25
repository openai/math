import OAI.Computability.BorderVNP.CubeRouteProfileInputs
import OAI.Computability.BorderVNP.CubeISALocalRowPinnedBoot

/-! # The signed scheduler's genuine boot operands on the profile memory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP.BurstRAM RoutingISA TeamContraction ProcessorSlots Packing
open RoutingISA.LocalRow RoutingOutputs
open private PinClear.read from OAI.Computability.BorderVNP.PackedHistoryPreparedInput

variable {w d : ℕ} (a : StartupArena) (u : Fin a.teams) (slot : ℕ) (packet : ReferencePacket w d)
    {f : BroadcastFrame} {A : AdviceLayout} {F : Pins.ProcessorFields (a.operands u slot packet).layout}
    {pub : Arg → Word w} {z : Bank w} {saved actual : Memory w}
    {bits : List Bool} (guess : ℕ → Bool)
local notation "L" => PacketOperands.layout (a.operands u slot packet)

/-- A real positive startup preserves all public scalar fields and every bit
of its parsed header on the selected pin. This holds for arbitrary payload
and padding outside the common header. -/
theorem signed_profile_pins (frame : (pub 0).val=a.frame)
    (boot : JointHeader.BootHeaderState F f A packet pub bits z saved)
    (resident : ∀ j < a.next, actual j=Pins.preparedMemory L guess saved (L).count j)
    (dst : f.dst=a.broadcastBase) (length : bits.length=a.header) :
    BootPins pub f packet.extension bits actual := by
  have inputs := profileRouteInputs_of_boot a u slot packet frame boot resident
  have extension := (resident_frames a u slot packet guess frame boot resident).2
  refine ⟨inputs.broadcast.1,inputs.broadcast.2.1,inputs.broadcast.2.2.2.2.2.2,extension,?_⟩
  intro i
  have bound : a.broadcastBase+a.header ≤ a.next := by
    unfold StartupArena.next StartupArena.hbase StartupArena.ibase
    omega
  have fit : i.val < a.header := length ▸ i.isLt
  rw [dst]
  refine (resident _ (by omega)).trans ?_
  exact (PinClear.read (arena_pin_clear a u slot packet).2.2 guess saved i.val fit).trans (dst ▸ boot.header i)

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
