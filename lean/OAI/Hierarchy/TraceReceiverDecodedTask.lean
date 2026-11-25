import OAI.Hierarchy.TraceReceiverIssuedCommands
import OAI.ThreeFlat.RAM.HistoryJoinWords

namespace OAI
/-! # Numerical child/parent records identify every field of the emitted terminal command -/
noncomputable section
namespace Hierarchy.TraceFactorReceiver.Issued
open ThreeFlat RAM Computability.VPVNP.BurstRAM PrivateRAM
open HistoryCommandTable HistoryJoinScan
open scoped Fin.CommRing

variable {W : ℕ}

theorem read_node (atNode stream pins rows bits : ℕ) (m : Memory W)
    (room : atNode+3<2^W)
    (s : m atNode=(stream:Word W)) (p : m (atNode+1)=(pins:Word W))
    (r : m (atNode+2)=(rows:Word W)) (b : m (atNode+3)=(bits:Word W)) :
    readNode m (atNode:Word W)=⟨stream,pins,rows,bits⟩ := by
  have address (j : Fin 4) : ((atNode:Word W)+(j.val:Word W)).val=atNode+j.val:=by
    rw [←Nat.cast_add,Fin.val_cast_of_lt (by have:=j.isLt;omega)]
  have same (j : Fin 4) := congrArg m (address j)
  unfold readNode
  congr 1
  · simpa using (same 0).trans (by simpa using s)
  · simpa using (same 1).trans p
  · simpa using (same 2).trans r
  · simpa using (same 3).trans b

/-- Decode one physically written task in the live command table. All
pointer and count preconditions refer to original words, before either
the command writer or its two-word cursor initializer executes. -/
theorem terminal_command (cursor commands tasks n : ℕ) (m : Memory W) (i : Fin n)
    (node parent stream oldPins rows internal base p map rowPrefix bitPrefix : ℕ)
    (below : cursor+2≤commands) (limit : commands+7*n<2^W)
    (task : readTask m ((tasks+5*i.val:ℕ):Word W)=
      ⟨(node:Word W),(parent:Word W),(map:Word W),(rowPrefix:Word W),(bitPrefix:Word W)⟩)
    (child : readNode m (node:Word W)=⟨(stream:Word W),oldPins,rows,internal⟩)
    (up : readNode m (parent:Word W)=⟨(base:Word W),p,0,0⟩) :
    let out:=image cursor commands tasks n m
    let h : Header ℕ:=⟨stream,base+4*rowPrefix,map,oldPins,p,bitPrefix⟩
    fetch ((commands+7*i.val:ℕ):Word W) out=h.words ∧
      out (commands+7*i.val+6)=((h.dest+4*rows:ℕ):Word W) := by
  have eqPtr : (tasks:Word W)+5*(i.val:Word W)=((tasks+5*i.val:ℕ):Word W):=by push_cast; rfl
  have hc:=fetch_task cursor commands tasks n m below limit i
  dsimp only at hc ⊢
  rw [eqPtr,task] at hc
  simpa only [child,up,Task.header,Task.past,Header.words,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,zero_add] using hc

end Hierarchy.TraceFactorReceiver.Issued
end

end OAI
