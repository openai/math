import OAI.Computability.BorderVNP.CubeRouteProfileInputs
import OAI.Computability.BorderVNP.CubeISALocalRowPinnedBoot

/-! # The chosen signed profile supplies the cube boot pins

The real profile path retains its own pin-prepared startup region. Its copied
header, all 81 literal extension words and ordinary packet frame thereby
supply the cube boot on the same returned memory and demand publication.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA TeamContraction ProcessorSlots Packing LocalRow

variable {w d k : ℕ} (start : StartupArena) (u : Fin start.teams) (slot : ℕ) (packet : ReferencePacket w d)
variable {F : Pins.ProcessorFields (start.operands u slot packet).layout} {f : BroadcastFrame} {A : AdviceLayout}
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {bits : List Bool} {bank : Bank w}
variable {initial profile : Memory w} {g : Fin k → Bool}

/-- The same returning path carries all physical startup operands through its
own signed substitutions and guarded geometry evaluation. -/
theorem BootResidence.profileOperands
    (path : BootResidence (F := F) start u slot packet f A pub mac bits initial bank g profile)
    (base : (pub 0).val = start.frame) (dst : f.dst = start.broadcastBase) (length : bits.length = start.header) :
    ProfileOperands F f A packet pub bits profile := by
  obtain ⟨_,_,saved,_,boot,resident⟩ := path
  obtain ⟨input,fr,_,_⟩ := routeInput_room start u slot packet F
  obtain ⟨inputClear,frameClear,copyClear⟩ := arena_pin_clear start u slot packet
  have prep := (ProfileOperands.from_boot boot).prepared (Pins.extendGuess g)
    (F.header_length ▸ inputClear) (base ▸ frameClear) (dst ▸ length ▸ copyClear)
  have copyRoom : f.dst+bits.length ≤ start.next := by
    rw [dst,length]
    unfold StartupArena.next StartupArena.hbase StartupArena.ibase
    omega
  refine ⟨fun j hj => (resident j (by omega)).trans (prep.input j hj),prep.frame.congr ?_,?_,?_⟩
  · intro i hi
    exact congrArg Fin.val (resident ((pub 0).val+i) (by omega))
  · intro i
    exact (resident _ (by have := i.isLt; omega)).trans (prep.extension i)
  · intro i
    exact (resident _ (by have := i.isLt; omega)).trans (prep.header i)

/-- The true reference packet reaches the subsequent public cube scheduler with
its extension intact and with the copied declaration still at its original
broadcast address. The compact rows use the native private and live placements. -/
theorem BootResidence.publishedPins {origin edges cells gap : ℕ} {placed : Memory w}
    (path : BootResidence (F := F) start u slot packet f A pub mac bits initial bank g profile)
    (base : (pub 0).val = start.frame) (dst : f.dst = start.broadcastBase) (length : bits.length = start.header)
    (D : Directory.Layout) (place : (RoutingOutputs.privateLayout start.frame origin edges cells
      D.entries D.description gap).Image (readings profile) D.entries (readings placed)) (room : start.next ≤ origin) :
    let tables := RoutingOutputs.bases origin edges cells D.entries
    let rows := D.directory (Directory.ISA.placement (readings placed) tables.privatePairs)
      (Directory.ISA.placement (readings placed) tables.livePairs)
    BootPins pub f packet.extension bits (Directory.ISA.publish placed start.frame start.next rows) := by
  intro tables rows
  have pins := BootPins.ofProfile (path.profileOperands start u slot packet base dst length) rfl
  have frame := (routeInput_room start u slot packet F).2.1
  have copied : f.dst+bits.length ≤ start.next := by
    rw [dst,length]
    unfold StartupArena.next StartupArena.hbase StartupArena.ibase
    omega
  have apart : (pub 0).val+9 < f.dst := by
    rw [base,dst]
    unfold StartupArena.broadcastBase StartupArena.dense
    omega
  rw [← base] at place ⊢
  exact pins.placedDirectory origin edges cells D.entries D.description gap start.next rows place
    (by omega) (copied.trans room) (base ▸ frame) copied (Or.inl apart)

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
