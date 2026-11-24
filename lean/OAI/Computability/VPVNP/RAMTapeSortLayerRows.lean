import OAI.Computability.VPVNP.RAMTapeSortLayerRowsProgram
import OAI.Computability.VPVNP.RAMTapeSortRowCross
import OAI.Computability.VPVNP.RAMTapeSortRowLocal

/-!
# Physical execution of a complete sorting layer

The fixed row traversal implements the local and cross-site comparators on
arbitrary five-word inputs. It preserves the input block, consumes exactly
the two exchange fields when the stride crosses sites, and accumulates the
selected records and every canonicality and outgoing-copy check.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortLayerRows

open BurstRAM RAMSort RAMBoundary Boundary

variable {h d w : ℕ}

theorem recordVisit_all (s : Stage (h+d)) (v : Word d) (current send recv : Wires h (RawSlot w))
    (next sendTail recvTail flags : List Bool) (i : Word h) :
    recordVisit s v current send recv next sendTail recvTail flags i := by
  let cur := blockBytes (List.ofFn current)
  let output := pushed (selected s v current recv) next i.val
  let ss := pending s send sendTail i.val
  let rr := pending s recv recvTail i.val
  let fs := latched (checks s current send recv) flags i.val
  let data := bank v s.phase s.stride w cur output ss rr fs
  let rs := prepared s v i data ∘ rowPorts
  have hready := prepared_ready s v i current output ss rr fs
  change SortRow.Ready rs current i (peerIndex s i) (decide (s.stride < h)) (keepMin s v i) at hready
  change ∃ t ≤ _, SortRow.program.Runs t rs (SortRow.result rs _ _ _ _ _ _)
  have hs : rs .crossSend = pending s send sendTail i.val := rfl
  have hr : rs .crossReceive = pending s recv recvTail i.val := rfl
  by_cases hj : s.stride < h
  · rw [decide_eq_true hj] at hready
    have run := SortRow.program_local_runs rs current i (peerIndex s i) (keepMin s v i) hready
    simpa only [other, hj, ↓reduceIte, hs, hr, pending] using run
  · rw [decide_eq_false hj] at hready
    have hsend := hs.trans (pending_cross hj send sendTail i)
    have hrecv := hr.trans (pending_cross hj recv recvTail i)
    have run := SortRow.program_cross_runs rs current i (peerIndex s i) (keepMin s v i) (send i) (recv i)
      (pending s send sendTail (i.val+1)) (pending s recv recvTail (i.val+1)) hready hsend hrecv
    simpa only [other, hj, ↓reduceIte] using run


/-- Complete row traversal at the word width of the five-word record format. -/
theorem runs (_hw : 2 ≤ w) (s : Stage (h+d)) (v : Word d) (current send recv : Wires h (RawSlot w))
    (next sendTail recvTail flags : List Bool) :
    ∃ t ≤ budget h d w s.phase s.stride, program.Runs t
      (SortOffsets.idle (bank v s.phase s.stride w (blockBytes (List.ofFn current)) next
        (fieldsBefore s send sendTail) (fieldsBefore s recv recvTail) flags) h)
      (SortOffsets.idle (bank v s.phase s.stride w (blockBytes (List.ofFn current))
        ((blockBytes (List.ofFn (selected s v current recv))).reverse ++ next) sendTail recvTail
        ((List.ofFn (checks s current send recv)).reverse.flatten ++ flags)) h) :=
  runs_of_visits s v current send recv next sendTail recvTail flags
    (recordVisit_all s v current send recv next sendTail recvTail flags)

end RAMTape.SortLayerRows

end VPVNP
end Computability
end OAI
