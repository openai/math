import OAI.Computability.VPVNP.RAMTapeSuccessorSharedValues
import OAI.Computability.VPVNP.RAMSortIncident

/-!
# From physical successor registers to the site's RAM cuts

The validator's word-level successor scan specifies the input and output cuts
and the two last records for the boundary check. On canonical incident fields
the physical stacks contain those same values, including the initial cut and
the missing output at the ends of the site chain.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Successors

open BurstRAM RAMLayout RAMSerialization RAMMemory

variable {d e w : ℕ}

/-- The word stacks at a missing send contain the zero, nonrunning cut. The
separate presence stack distinguishes it from a present halted target. -/
def sideCut (summary : SiteSuccessors w) : Side → Cut w
  | .send => summary.output.getD ⟨0, none⟩
  | .receive => summary.input

/-- Select the optional sent or received boundary record from a site's successor summary. -/
def sideRecord (summary : SiteSuccessors w) : Side → Option (Record (Word w))
  | .send => summary.sent
  | .receive => summary.received

/-- Register contents in terms of the word validator. Each cost occupies a
full word and has the stated natural value. Each record's encoded words
widen to the actual address, timestamp and ordinal in the transcript. -/
structure CutRegisters (base out : Stacks Port) (hw : 2 ≤ w) (summary : SiteSuccessors w)
    (suffix : List Bool) : Prop where
  incident : out .incident = suffix
  outPresent : out .outPresent = summary.output.isSome :: base .outPresent
  running : ∀ side, out (.running side) = (sideCut summary side).state.isSome :: base (.running side)
  cost : ∀ side, ∃ x : Word w, out (.word side 1) = BurstRAM.wordBits x ∧ x.val = (sideCut summary side).cost
  state : ∀ side, out (.word side 2) = BurstRAM.wordBits ((sideCut summary side).state.getD 0)
  record : ∀ side, ∃ r : Option (WordRecord w), r.map WordRecord.record = sideRecord summary side ∧
    out (.record side) = List.ofFn ((recordFormat hw).encode r) ++ base (.record side)

private theorem summary_out (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (initial : Word w)
    (a : SendArrays d (2^e) w) (v : Fin (2^d)) (summary : SiteSuccessors w)
    (h : summary.Spec hw hc initial v a) :
    summary.output.isSome = (sentMessage hw hc a v).isSome := by
  rw [h.output_eq, outputCut, sentMessage]
  split <;> rfl

private theorem summary_cut (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (initial : Word w)
    (a : SendArrays d (2^e) w) (v : Fin (2^d)) (summary : SiteSuccessors w)
    (h : summary.Spec hw hc initial v a) (side : Side) :
    let msg := atSide (sentMessage hw hc a v) (receivedMessage hw hc a v) side
    sideCut summary side = ⟨(costWord hc msg).val, savedState initial side msg⟩ := by
  cases side with
  | send =>
    change summary.output.getD _ = ⟨_, _⟩
    rw [h.output_eq, outputCut]
    by_cases hv : v.val + 1 < 2^d <;>
      simp [atSide, sentMessage, hv, costWord, savedState, unpackMessages]
  | receive =>
    change summary.input = ⟨_, _⟩
    rw [h.input_eq, inputCut]
    by_cases hv : v.val = 0
    · simp [atSide, receivedMessage, hv, costWord, savedState]
    · have hpos : 0 < v.val := by omega
      simp [atSide, receivedMessage, hv, hpos, costWord, savedState, unpackMessages]

private theorem summary_record (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (initial : Word w)
    (a : SendArrays d (2^e) w) (v : Fin (2^d)) (summary : SiteSuccessors w)
    (h : summary.Spec hw hc initial v a) (side : Side) :
    let msg := atSide (sentMessage hw hc a v) (receivedMessage hw hc a v) side
    (msg.bind (·.lastRecord)).map WordRecord.record = sideRecord summary side := by
  cases side with
  | send =>
    change ((sentMessage hw hc a v).bind (·.lastRecord)).map WordRecord.record = summary.sent
    rw [h.sent_eq, RAMBoundary.outgoing, sentMessage]
    split <;> rfl
  | receive =>
    change ((receivedMessage hw hc a v).bind (·.lastRecord)).map WordRecord.record = summary.received
    rw [h.received_eq]
    rcases v with ⟨i, hi⟩
    cases i <;> rfl

/-- Identify physical register outputs with any typed summary satisfying the
site successor specification. The lemma applies before and after the guard. -/
theorem Outputs.cutRegisters {hw : 2 ≤ w} {hc : 2^d * 2^e < 2^w} {initial : Word w}
    {s out : Stacks Port} {a : SendArrays d (2^e) w} {v : Fin (2^d)} {suffix : List Bool}
    (registers : Outputs s out hw hc initial (sentMessage hw hc a v) (receivedMessage hw hc a v) suffix)
    (summary : SiteSuccessors w) (hs : summary.Spec hw hc initial v a) :
    CutRegisters s out hw summary suffix := by
  have hcut := summary_cut hw hc initial a v summary hs
  have hrecord := summary_record hw hc initial a v summary hs
  refine ⟨registers.incident, ?_, ?_, ?_, ?_, ?_⟩
  · rw [summary_out hw hc initial a v summary hs]
    exact registers.outPresent
  · intro side
    rw [hcut side]
    exact registers.running side
  · intro side
    rw [hcut side]
    exact ⟨_, registers.cost side, rfl⟩
  · intro side
    rw [hcut side]
    exact registers.state side
  · intro side
    exact ⟨_, hrecord side, registers.record side⟩

/-- At the continuation of the guard, the exact stack representation agrees
with the word validator's successor scan on the same site and shared bits. -/
theorem guarded_cutRegisters (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (initial : Word w)
    (a : SendArrays d (2^e) w) (v : Fin (2^d)) (s : Stacks Port)
    (hi : s .initial = BurstRAM.wordBits initial) (hs : SuccessorSendOK hw hc a v)
    (hr : SuccessorReceiveOK hw hc a v) :
    CutRegisters s (guardResult (sharedFinish hc a v s)) hw
      (scanSuccessors hw hc initial v (sortIncident a v)).1
      ((List.ofFn (RAMLayout.incidentBits a v)).drop (16*w)) :=
  (guard_shared_values hw hc a v s initial hi hs hr).cutRegisters _
    (scanSuccessors_spec hw hc initial v (sortIncident a v) a (sortIncident_offset a v))

end RAMTape.Successors

end VPVNP
end Computability
end OAI
