import OAI.Hierarchy.DescentTerminalResetRoleArity
import OAI.Hierarchy.DescentPhysicalResetRoleFrames
import OAI.Hierarchy.DescentPhysicalRoleRooms

namespace OAI
/-! # Paid and span operands at the exact input to the node metadata writer -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentSixParty DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "venue" => (v).venue
local notation "fund" => (v).fundedEnd b
local notation "roleAt" => (v).fullEnd b
local notation "movedAt" => (v).roleEnd b
local notation "classAt" => (v).classEnd b
local notation "bornAt" => (v).birthEnd b
local notation "meta" => (v).primitiveEnd b

/-- All earlier words survive the role publisher and the primitive instruction,
including every packed-span and paid-count input of the final metadata writer. -/
theorem metadata_input_frames (ready : u.Ready) (fit : z.Room) (mid : Memory w)
    (blocks : (v).metadata.chart.blocks≤2^(venue).next.k) :
    let entry:=z.tokenImage (z.roleInput mid)
    let board:=z.venueImage mid
    (∀x,x<roleAt→entry x=board x) ∧
    (∀x r,(paid u x).eval entry r=(paid u x).eval board r) ∧
    ∀x node j r,(z.spans x node j).eval entry r=(z.spans x node j).eval board r :=by
  intro entry board
  have moved:roleAt≤ movedAt:=by rw [ResetOutput.roleEnd,(v).roleTransfer.translate];exact Nat.le_add_right ..
  have classified:movedAt≤classAt:=((v).actorClass.guard movedAt).1.trans ((v).actorClass.guard movedAt).2
  have born:classAt≤bornAt:=by rw [ResetOutput.birthEnd,(v).birth.translate];exact Nat.le_add_right ..
  have roof:meta≤a.endAddress floor:=by change _≤(v).metadata.endAddress meta;rw [(v).metadata.translate];exact Nat.le_add_right ..
  have run_:=(v).primitive.any z.menu.gadget z.menu.stageBits z.menu.grain z.menu.op bornAt z.roles
    (z.roleInput mid) fit.roleFields (roof.trans_lt fit.endFits)
  have same:∀x,x<roleAt→entry x=board x:=by
    intro x h
    exact (run_.2.2 x (.inl (h.trans_le (moved.trans (classified.trans born))))).trans
      ((z.role_input_frames fit mid).2.2 x (.inl h))
  refine ⟨same,?_,?_⟩
  · intro x r
    let idx : Fin (2^(venue).next.k):=⟨x.val,x.isLt.trans_le blocks⟩
    have read:=(fit.successor.return_.paid idx).1
    have low:(venue).venueStart fund≤roleAt:=((venue).after fund).2.2
    apply eval_below _ _ _ _ (out:=roleAt) _ same
    exact ⟨⟨read.1,read.2.1,read.2.2.trans low⟩,trivial⟩
  · intro x node j r
    obtain ⟨old,fresh⟩:=(v).complete_after b
    exact eval_below _ _ _ _ (z.span_at ready x node j) (fun n h=>same n (h.trans_le (old.trans fresh)))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
