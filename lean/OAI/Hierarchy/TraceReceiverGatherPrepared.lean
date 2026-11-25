import OAI.Hierarchy.TraceReceiverLiveRows

namespace OAI
/-! # Completing the physical gather precondition from selected per-root word receipts -/
noncomputable section
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat RAM HistoryJoinScan Diagonal.HistoryContraction
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] {W n p : ℕ} {arity : Fin n→ℕ}
variable (nets : ∀ i,BitNetwork F (arity i)) (wires : ∀ i,Fin (arity i)→Fin p)
variable (pin : Fin p→Bool) (base ctrl control H commands : ℕ) (m : Memory W)
set_option quotPrecheck false
local notation "cells" => (fun i => (nets i).cells)
local notation "spans" => (List.ofFn (rootSpan base cells))
local notation "tag" => (fun t : (Fin 3→Bool)→F => (Fintype.equivFin _ t).val)

/-- The destination stream is a single ordered S9 arena. Its numeric
upper endpoint plus the independently verified S12/sector30 frames are
sufficient to protect all preceding commands, the input pins and S18. -/
theorem prepared_of_issued (layout : ctrl+2≤commands) (commandRoom : commands+7*n<2^W)
    (forestRoom : base+4*(∑ i,cells i)≤ctrl) (scalars : base+4*(∑ i,cells i)≤control+2)
    (ctrlRoom : control+3<ctrl) (pinRoom : BitLayout.cellsBase p H≤base)
    (initial : m ctrl=(commands:Word W)) (last : m (ctrl+1)=((commands+7*n:ℕ):Word W))
    (counts : m (control+2)=((forest nets wires).cells:Word W) ∧
      m (control+3)=((forest nets wires).internal:Word W))
    (pins : ∀ a<BitLayout.cellsBase p H,m a=TickMountedPins.memory pin a)
    (data : ∀ i : Fin n,∃ head mapping,
      IssuedRoot nets wires tag (ctrl:Word W) base commands m i head mapping ∧
      m (commands+7*i.val+6)=((head.dest+4*cells i:ℕ):Word W)) :
    Prepared nets (ctrl:=ctrl) (control:=control) (H:=H) (atCmd:=commands) wires pin base spans m := by
  let c:Word W:=ctrl
  have cval : c.val=ctrl:=Fin.val_cast_of_lt (by omega)
  have bounds (s : Span) (inList : s∈spans) : base≤ s.dest ∧ s.stop≤base+4*(∑ i,cells i):=by
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp inList
    have h:=Tree.prefix_next_le cells i
    change base≤base+4*Tree.before cells i ∧ base+4*Tree.before cells i+4*cells i≤_
    refine ⟨Nat.le_add_right _ _,?_⟩
    simpa only [Nat.mul_add,Nat.add_assoc] using Nat.add_le_add_left (Nat.mul_le_mul_left 4 h) base
  have off (s : Span) (hs : s∈spans) : c.val< s.dest ∨ s.stop≤c.val:=
    Or.inr ((bounds s hs).2.trans (forestRoom.trans_eq cval.symm))
  have roots (i : Fin n) := (data i).imp (fun h proof=>proof.imp fun _ x=>x.1)
  have current : m c.val=(commands:Word W):=by simpa only [cval] using initial
  have endCmd : commands+7*(spans).length<2^W:=by simpa using commandRoom
  refine ⟨layout,endCmd,initial,by simpa using last,?_,?_,?_,?_,
    issued_safe current off roots,issued_locations current (.inr (forestRoom.trans_eq cval.symm)) off roots,
    counts,pins,?_⟩
  · intro i
    let j : Fin n:=⟨i.val,by simpa using i.isLt⟩
    obtain ⟨head,mapping,r,endWord⟩:=data j
    have atSpan : (spans).get i=rootSpan base cells j:=by simp [j,List.get_eq_getElem]
    have dest:=congrArg Header.dest r.cmd
    change m ((((commands+7*j.val:ℕ):Word W)+1).val)=(head.dest:Word W) at dest
    rw [←Nat.cast_one (R:=Word W),←Nat.cast_add,Fin.val_cast_of_lt (by have:=j.isLt;omega)] at dest
    rw [atSpan]
    exact ⟨dest.trans (congrArg (fun a:ℕ=>(a:Word W)) r.dest),by simpa only [r.dest,rootSpan,Span.stop] using endWord⟩
  · intro s hs
    exact Or.inl ((bounds s hs).2.trans forestRoom)
  · intro s hs
    exact Or.inl ((bounds s hs).2.trans (by omega))
  · intro s hs
    exact lt_of_le_of_lt ((bounds s hs).2.trans forestRoom) (by omega)
  · intro a ha
    constructor
    · change a≠c.val
      rw [cval]
      rcases ha with h|h|h <;> omega
    · intro s hs
      obtain ⟨lo,hi⟩:=bounds s hs
      rcases ha with h|h|h
      · exact Or.inr (by omega)
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)

end Hierarchy.TraceFactorReceiver.Gather
end

end OAI
