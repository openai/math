import OAI.Hierarchy.TraceReceiverGridWindow
import OAI.Hierarchy.TraceReceiverMapHeader
import OAI.Hierarchy.TraceReceiverRootFrame

namespace OAI
/-! # Word and interval bounds of the actual terminal gather banks -/

noncomputable section
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat Diagonal Diagonal.HistoryContraction RAM
open Computability.VPVNP.BurstRAM PrivateRAM HistoryCompiledRows HistoryJoinScan
open scoped BigOperators Fin.CommRing Classical

variable {w u n : ℕ}


/-- Every canonical output span in a gather prefix belongs to its true
four-word S9 allocation. -/
theorem untouched_s9 (rows : Fin n → ℕ) (base take a : ℕ) (ctrl : Word w)
    (different : a≠ctrl.val) (outside : a<base ∨ base+4*(∑ j,rows j)≤a) :
    Untouched ctrl ((List.ofFn (rootSpan base rows)).take take) a := by
  refine ⟨different,?_⟩
  intro span member
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take member)
  have limit:=Tree.prefix_next_le rows i
  change a<base+4*Tree.before rows i ∨ base+4*Tree.before rows i+4*rows i≤a
  omega

variable {F : Type*} {arity : Fin n → ℕ}

/-- The four numeric constraints for an emitter's original S12 record and
the saved sector-30 pin map. The arity prefix is the scan of the same roots. -/
theorem gather_room (nets : ∀ i,BitNetwork F (arity i)) (tag : ((Fin 3→Bool)→F)→ℕ)
    (large : 7≤w) (age : u^10≤5*w) (i : Fin n) (head : Header ℕ)
    (stream : head.source+4*(nets i).cells≤TickWorkspace.base u 14)
    (saved : head.pins=(GridReceiverBanks.tasks w).maps+Tree.before arity i)
    (pins : head.oldPins=arity i) (total : (∑ j,arity j)≤GridReceiverBanks.gap w)
    (hidden : (nets i).internal≤GridReceiverBanks.gap w)
    (tables : ∀ t,tag t<2^(64*w)) :
    head.source+4*(nets i).cells≤2^(64*w) ∧ head.pins+head.oldPins≤2^(64*w) ∧
      2+head.oldPins<2^(64*w) ∧ ∀ r c,metadata tag (nets i) r c<2^(64*w) := by
  obtain ⟨bank,roof,slots⟩ := grid_window large age
  have page:=TickWorkspace.apart (u:=u) (by decide : 14<45)
  have quota:=(Tree.prefix_next_le arity i).trans total
  have stored : head.pins=GridReceiverBanks.base w+2*GridReceiverBanks.gap w+Tree.before arity i := saved
  rw [pins]
  refine ⟨by omega,by omega,by omega,metadata_fits tag (nets i) (by omega) tables⟩

/-- Source, pin-map and six command words all survive preceding S9 copies.
The cursor occupies its reserved word at offset 32 of sector 30. -/
theorem gather_untouched (rows : Fin n → ℕ) (large : 7≤w) (age : u^10≤5*w)
    (i : Fin n) (count : n≤GridReceiverBanks.gap w)
    (size : 4*(∑ j,rows j)≤TickWorkspace.stride u) :
    let B:=GridReceiverBanks.base w
    let G:=GridReceiverBanks.gap w
    let cursor:=(GridReceiverBanks.cursor w:Word (64*w))
    let rootBase:=TickWorkspace.base u 9
    let previous:=(List.ofFn (rootSpan rootBase rows)).take i.val
    GridReceiverBanks.commands w+7*n<2^(64*w) ∧
    (∀ a,TickWorkspace.base u 12≤a→a<TickWorkspace.base u 14→Untouched cursor previous a) ∧
    (∀ a,B+2*G≤a→a<B+3*G→Untouched cursor previous a) ∧
    (∀ c : Fin 6, Untouched cursor previous
      (((GridReceiverBanks.commands w+7*i.val:ℕ):Word (64*w))+(c.val:Word (64*w))).val) := by
  intro B G cursor rootBase previous
  obtain ⟨bank,roof,slots⟩:=grid_window large age
  have old:=TickWorkspace.apart (u:=u) (by decide : 9<12)
  have high:=TickWorkspace.apart (u:=u) (by decide : 14<45)
  have mid:=TickWorkspace.apart (u:=u) (by decide : 12<14)
  have low : rootBase+4*(∑ j,rows j)≤TickWorkspace.base u 12 := by dsimp only [rootBase];omega
  have cursorVal : cursor.val=B+32 := Fin.val_cast_of_lt (by omega : B+32<2^(64*w))
  have cmd : GridReceiverBanks.commands w=B+9*G := rfl
  have qi:=i.isLt
  refine ⟨by rw [cmd];omega,?_,?_,?_⟩
  · intro a left right
    apply untouched_s9 rows rootBase i.val a cursor (by rw [cursorVal];omega)
    exact Or.inr (low.trans left)
  · intro a left right
    apply untouched_s9 rows rootBase i.val a cursor (by rw [cursorVal];omega)
    exact Or.inr (by omega)
  · intro c
    have j:=c.isLt
    rw [←Nat.cast_add,Fin.val_cast_of_lt (by rw [cmd];omega)]
    apply untouched_s9 rows rootBase i.val _ cursor (by rw [cursorVal,cmd];omega)
    exact Or.inr (by rw [cmd];omega)

/-- The concrete three-word map-save header is below every five-word task
and saved pin map. The S14 scratch and saved maps fit the word modulus. -/
theorem save_room (large : 7≤w) (age : u^10≤5*w) (i : Fin n)
    (total : (∑ j,arity j)≤GridReceiverBanks.gap w) :
    let hdr:=GridReceiverBanks.mapHeader w
    let dst:=(GridReceiverBanks.tasks w).maps+Tree.before arity i
    let src:=TickWorkspace.base u 14+64
    hdr+3<2^(64*w) ∧ hdr+3≤dst ∧ dst+arity i<2^(64*w) ∧ src+arity i≤2^(64*w) ∧ src+arity i≤dst := by
  intro hdr dst src
  obtain ⟨bank,roof,slots⟩:=grid_window large age
  have lower:=TickWorkspace.apart (u:=u) (by decide : 14<45)
  have used:=(Tree.prefix_next_le arity i).trans total
  change GridReceiverBanks.base w+24+3<2^(64*w) ∧
    GridReceiverBanks.base w+24+3≤GridReceiverBanks.base w+2*GridReceiverBanks.gap w+Tree.before arity i ∧
    GridReceiverBanks.base w+2*GridReceiverBanks.gap w+Tree.before arity i+arity i<2^(64*w) ∧
    TickWorkspace.base u 14+64+arity i≤2^(64*w) ∧
    TickWorkspace.base u 14+64+arity i≤GridReceiverBanks.base w+2*GridReceiverBanks.gap w+Tree.before arity i
  omega

/-- Reading the ordinal, the selected five-word task and the S13 child
pin-count cannot touch the three words the map seed is writing. -/
theorem save_sample_room (large : 7≤w) (age : u^10≤5*w) (i : Fin n)
    (jobs : 5*n≤GridReceiverBanks.gap w) (m : Memory (64*w)) (node : ℕ)
    (ord : m (TickWorkspace.base u 18)=(i.val:Word (64*w)))
    (child : m ((GridReceiverBanks.tasks w).tasks+5*i.val)=(node:Word (64*w)))
    (loc : node+1<TickWorkspace.base u 14) :
    ∀ a, TraceReceiverMapSave.sample (GridReceiverBanks.tasks w).tasks (TickWorkspace.base u 18) m a →
      a<GridReceiverBanks.mapHeader w ∨ GridReceiverBanks.mapHeader w+3≤a := by
  let B:=GridReceiverBanks.base w
  let G:=GridReceiverBanks.gap w
  obtain ⟨bank,roof,slots⟩:=grid_window large age
  have ordLow:=TickWorkspace.apart (u:=u) (by decide : 18<45)
  have childLow:=TickWorkspace.apart (u:=u) (by decide : 14<45)
  have step:=i.isLt
  have ordval : ((TickWorkspace.base u 18:ℕ):Word (64*w)).val=TickWorkspace.base u 18 :=
    Fin.val_cast_of_lt (by omega)
  let t:=TraceReceiverMapSave.taskWord (GridReceiverBanks.tasks w).tasks (TickWorkspace.base u 18) m
  have task : t=((B+G+5*i.val:ℕ):Word (64*w)) := by
    dsimp only [t,TraceReceiverMapSave.taskWord]
    rw [ordval,ord]
    simp only [B,G,GridReceiverBanks.tasks,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have room : B+G+5*i.val+2<2^(64*w) := by omega
  have taskVal : t.val=B+G+5*i.val := by rw [task,Fin.val_cast_of_lt (by omega)]
  have next : (t+2).val=B+G+5*i.val+2 := by
    rw [task,←Nat.cast_ofNat (R:=Word (64*w)) (n:=2),←Nat.cast_add,Fin.val_cast_of_lt room]
  have endWord : (m t.val+1).val=node+1 := by
    rw [taskVal]
    change (m ((GridReceiverBanks.tasks w).tasks+5*i.val)+1).val=_
    rw [child,←Nat.cast_one (R:=Word (64*w)),←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
  intro a sampled
  change a=((TickWorkspace.base u 18:ℕ):Word (64*w)).val ∨ a=t.val ∨ a=(t+2).val ∨ a=(m t.val+1).val at sampled
  rcases sampled with ordAt|taskAt|nextAt|lastAt
  · left;change a<B+24;rw [ordval] at ordAt;omega
  · right;change B+24+3≤a;rw [taskVal] at taskAt;omega
  · right;change B+24+3≤a;rw [next] at nextAt;omega
  · left;change a<B+24;rw [endWord] at lastAt;omega

end Hierarchy.TraceFactorReceiver.Gather

end
end OAI
