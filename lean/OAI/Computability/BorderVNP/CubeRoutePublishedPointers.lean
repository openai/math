import OAI.Computability.BorderVNP.CubeRoutePinnedFrame
import OAI.Computability.BorderVNP.CubeRouteProfileInputs

/-! # Pinned scheduler pointers after the actual delivery-directory publication -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction TeamContraction.ProcessorSlots Packing RoutingOutputs

variable {w d : ℕ} (task : SignedTaskArena.Layout) (start : StartupArena) (team : Fin start.teams)
variable (slot : ℕ) (p : ReferencePacket w d)

/-- The true time-zero public scalar choices are still the routing table pointers at the
entry of the group schedule, after private placement and publishing the compacted delivery rows. -/
theorem BootResidence.demandPointers {k entries desc gap : ℕ} (count : ℕ) (other : Arg → Word w)
    (origin edges cells : ℕ) {f : BroadcastFrame} {advice : AdviceLayout} {mac : TeamOpcode.Macros w 8}
    {bits : List Bool} {bank : Bank w} {initial after placed : Memory w} {g : Fin k → Bool}
    (room : task.cube.stop < 2^w) :
    let B := start.operands team slot p
    let pub := B.bank (core (task.routeBank start.frame other) origin edges cells)
    B.Fits w → ∀ {F : Pins.ProcessorFields B.layout},
      BootResidence (F := F) start team slot p f advice pub mac bits initial bank g after →
      (privateLayout start.frame origin edges cells entries desc gap).Image (readings after) entries (readings placed) →
      start.next ≤ origin → ∀ rows : List Directory.Row,
      TablePointers (task.cube.table start.frame count) (readings (Directory.ISA.publish placed start.frame start.next rows)) := by
  intro B pub fits F history placement reserve rows
  obtain ⟨_,_,_,_,boot,resident⟩ := history
  have old := pinnedTablePointers_of_profile task start team slot count p other origin edges cells
    (Pins.extendGuess g) room fits boot resident
  apply old.transfer
  intro j hj
  have small : j < 112 ∧ j ≠ 9 := by simp at hj; omega
  have low : start.frame+j < start.next := by
    dsimp only [StartupArena.next,StartupArena.hbase,StartupArena.ibase,StartupArena.broadcastBase,StartupArena.dense]
    omega
  exact congrArg Fin.val (directoryPublished_low rows placement reserve (start.frame+j) low (fun eq => small.2 (Nat.add_left_cancel eq)))

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
