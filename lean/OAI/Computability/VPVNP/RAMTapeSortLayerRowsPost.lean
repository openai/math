import OAI.Computability.VPVNP.RAMTapeSortLayerRowsPorts
import OAI.Computability.VPVNP.RAMTapeSortRowModel

/-!
# Installing a record comparison in the row traversal

The partner offset and decision bits produced by the address routine satisfy
the record routine's input conditions. A comparison changes the pending
output, exchange streams and flags. The traversal retains its binary and
unary row indices for the subsequent increment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortLayerRows

open BurstRAM RAMSort RAMBoundary Boundary

/-- The address computation has prepared all record operands and scratch stacks. -/
theorem prepared_ready {h d w : ℕ} (s : Stage (h+d)) (v : Word d) (i : Word h)
    (block : Word h → RawSlot w) (next send recv flags : List Bool) :
    SortRow.Ready
      (prepared s v i (bank v s.phase s.stride w (blockBytes (List.ofFn block)) next send recv flags) ∘ rowPorts)
      block i (peerIndex s i) (decide (s.stride < h)) (keepMin s v i) := by
  constructor <;> first | rfl | constructor <;> rfl

/-- Install a record routine's execution on the layer ports. The next row
will see the selected record and flags at the heads of their reverse streams. -/
theorem row_run {h d w t : ℕ} (s : Stage (h+d)) (v : Word d) (i : Word h)
    (cur next send recv flags : List Bool) (a b : RawSlot w) (sent : Option (RawSlot w))
    (sendTail recvTail : List Bool) (prog : FiniteRoutine SortRow.Port)
    (hr : let rs := prepared s v i (bank v s.phase s.stride w cur next send recv flags) ∘ rowPorts
          prog.Runs t rs (SortRow.result rs (keepMin s v i) a b sent sendTail recvTail)) :
    (prog.onPorts rowPorts).Runs t
      (prepared s v i (bank v s.phase s.stride w cur next send recv flags))
      (SortOffsets.visit (bank v s.phase s.stride w cur
        ((recordBytes (SortRow.chosen (keepMin s v i) a b)).reverse ++ next) sendTail recvTail
        (SortRow.selectOK a b :: sent.elim flags (fun x => SortRow.verifyOK a x :: flags))) i) := by
  apply FiniteRoutine.runs_onPorts_framed _ rowPorts_injective hr
  · intro p; rfl
  · intro p; cases p <;> rfl
  · intro p hp
    rcases p with (r | e) | f
    · cases r <;> first | rfl | exact (hp .next rfl).elim
                            | exact (hp .crossSend rfl).elim | exact (hp .crossReceive rfl).elim
                            | exact (hp .partner rfl).elim | exact (hp .orientation rfl).elim
                            | exact (hp .localFlag rfl).elim | exact (hp .flags rfl).elim
    · cases e <;> rfl
    · rfl

end RAMTape.SortLayerRows

end VPVNP
end Computability
end OAI
