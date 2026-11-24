import OAI.Computability.VPVNP.RAMTapeSortLayerRowsModel
import OAI.Computability.VPVNP.RAMTapeSortLayerRowsPost
import OAI.Computability.VPVNP.RAMTapeSortRowProgram

/-!
# Composing the address, record and counter controls for one sorting layer
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortLayerRows

open BurstRAM RAMSort RAMBoundary Boundary

/-- Compute the partner and comparison direction from the row address, then execute the record
routine on that row. -/
def row : FiniteRoutine Port :=
  (SortRowAddress.routine.onPorts addressPorts).followedBy (SortRow.program.onPorts rowPorts)

/-- Use the finite row iterator to execute the address and record routines at every row in the
layer. -/
def program : FiniteRoutine Port := SortOffsets.routine row

variable {h d w : ℕ} (s : Stage (h+d)) (v : Word d) (current send recv : Wires h (RawSlot w))
  (next sendTail recvTail flags : List Bool)

/-- The physical record subroutine consumes the two field heads precisely on
a nonlocal stride. The next unread message offsets are the suffixes at `i+1`. -/
def recordVisit (i : Word h) : Prop :=
  let data := prefixBank s v current send recv next sendTail recvTail flags i.val
  let rs := prepared s v i data ∘ rowPorts
  ∃ t ≤ 4096*(2^h+1)*(w+1), SortRow.program.Runs t rs
    (SortRow.result rs (keepMin s v i) (current i) (other s current recv i)
      (if s.stride < h then none else some (send i))
      (pending s send sendTail (i.val+1)) (pending s recv recvTail (i.val+1)))

/-- Each address preparation reaches the exact inputs of the record routine.
The outputs update all four streams for the subsequent row. -/
theorem visit_run (i : Word h) (hr : recordVisit s v current send recv next sendTail recvTail flags i) :
    let data := prefixBank s v current send recv next sendTail recvTail flags
    ∃ t ≤ SortRowAddress.budget h d s.phase s.stride + 4096*(2^h+1)*(w+1),
      row.Runs t (SortOffsets.visit (data i.val) i) (SortOffsets.visit (data (i.val+1)) i) := by
  let cur := blockBytes (List.ofFn current)
  let output := pushed (selected s v current recv) next i.val
  let ss := pending s send sendTail i.val
  let rr := pending s recv recvTail i.val
  let fs := latched (checks s current send recv) flags i.val
  obtain ⟨t,ht,ha⟩ := address_run s v i cur output ss rr fs
  obtain ⟨u,hu,hrec⟩ := hr
  have hrun := row_run s v i cur output ss rr fs (current i) (other s current recv i)
    (if s.stride < h then none else some (send i)) (pending s send sendTail (i.val+1))
    (pending s recv recvTail (i.val+1)) SortRow.program hrec
  have he :
      SortRow.selectOK (current i) (other s current recv i) ::
        (if s.stride < h then none else some (send i)).elim fs (fun x => SortRow.verifyOK (current i) x :: fs) =
      checks s current send recv i ++ fs := by
    by_cases hj : s.stride < h <;> simp [checks,hj]
  rw [he] at hrun
  refine ⟨_, Nat.add_le_add ht hu, ?_⟩
  simpa only [row, cur, output, ss, rr, fs, prefixBank, pushed_succ, latched_succ, selected] using
    (FiniteRoutine.Runs.followedBy ha hrun)

/-- The concrete counter traversal consumes the message blocks and accumulates
the selected rows and their flags. -/
theorem runs_of_visits
    (hr : ∀ i, recordVisit s v current send recv next sendTail recvTail flags i) :
    ∃ t ≤ budget h d w s.phase s.stride, program.Runs t
      (SortOffsets.idle (bank v s.phase s.stride w (blockBytes (List.ofFn current)) next
        (fieldsBefore s send sendTail) (fieldsBefore s recv recvTail) flags) h)
      (SortOffsets.idle (bank v s.phase s.stride w (blockBytes (List.ofFn current))
        ((blockBytes (List.ofFn (selected s v current recv))).reverse ++ next) sendTail recvTail
        ((List.ofFn (checks s current send recv)).reverse.flatten ++ flags)) h) := by
  have hrun := SortOffsets.runs row (prefixBank s v current send recv next sendTail recvTail flags) h
    (SortRowAddress.budget h d s.phase s.stride + 4096*(2^h+1)*(w+1))
    (fun i => visit_run s v current send recv next sendTail recvTail flags i (hr i))
  simpa only [budget, program, prefixBank_zero, prefixBank_all] using hrun

end RAMTape.SortLayerRows

end VPVNP
end Computability
end OAI
