import OAI.Hierarchy.ProtocolRAMBatchInputEnd
import OAI.Hierarchy.ProtocolRAMCalendarPostLayout

namespace OAI
/-! # Input sources for the entire post-purchase native column program -/

namespace Hierarchy.ProtocolRAM.PurchaseStage
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
variable {q d cut w : ℕ}

structure LinkInputs (l : Link) (cut : ℕ) : Prop where
  group : l.group.inputEnd≤cut
  endpoint : l.endpoint.inputEnd≤cut
  opposite : l.opposite.inputEnd≤cut
  length : l.lengthCode.inputEnd≤cut

structure SnapshotReads (L : Dispatch) (B : Repair q d) (cut : ℕ) : Prop where
  ballot : (enabledBatch L B).Before cut
  selected : decisionBase L+2^B.decisionBits≤cut
  stop : B.policy.stop.base+B.policy.stop.size≤cut
  excess : B.policy.excess.base+B.policy.excess.size≤cut
  payload : B.policy.payload.base+B.policy.payload.size≤cut
  discrepancy : B.policy.discrepancy.base+B.policy.discrepancy.size≤cut
  link : LinkInputs B.link cut
  purchase : LinkInputs B.purchaseLink cut
  menu : B.purchaseMenu.inputEnd≤cut
  printed : ∀i,(B.reportWidth i).inputEnd≤cut
  wire : ∀i j,(B.wire i j).inputEnd≤cut
  reserve : ∀i,(B.reserve i).inputEnd≤cut
  half : B.halfTable.base+B.halfTable.size≤cut
  feed : B.feedTable.base+B.feedTable.size≤cut

namespace SnapshotReads
variable {L : Dispatch} {B : Repair q d} (h : SnapshotReads L B cut)
include h

theorem mode : (AttemptGate.mode B.policy).inputEnd≤cut := by
  cases ex : B.policy.reserve <;> cases ey : B.policy.injection <;>
    simp only [AttemptGate.mode,ex,ey,Bool.false_eq_true,ite_true,ite_false,AttemptGate.nonzero,Expr.inputEnd,max_le_iff,Nat.zero_le,
      and_true,h.stop,h.excess,h.payload,h.discrepancy]

theorem buy : (buyWord L B).inputEnd≤cut := by
  simp only [buyWord,AttemptGate.ifPurchase,AttemptGate.ifMode,Expr.inputEnd,max_le_iff,
    Nat.zero_le,and_true,h.mode,Bank.size,h.selected]

private theorem funded (i : Fin d) : (fedStock B i).inputEnd≤cut := by
  have balance : (B.batch.stock i).inputEnd≤cut:=h.ballot.stock i
  simp only [fedStock,ProtocolRAM.feed,Expr.inputEnd,max_le_iff,Nat.zero_le,and_true,h.feed,h.reserve,balance]

private theorem endStock (i : Fin d) :
    (retained L B i).inputEnd≤cut ∧ (discharge B i).inputEnd≤cut ∧ (saved B i).inputEnd≤cut := by
  have prev : (B.batch.stock i).inputEnd≤cut:=h.ballot.stock i
  have updated:=h.ballot.nextStock i _ (h.ballot.wire _ (h.wire i))
  have bound:=h.funded i
  have held:=h.reserve i
  cases adv:B.feedOnAdvance <;>
    simp only [retained,discharge,saved,AttemptGate.ifRepair,AttemptGate.ifPurchase,AttemptGate.ifAdvance,
      AttemptGate.ifMode,StockAccounts.overflow,StockAccounts.clipped,adv,Bool.false_eq_true,ite_true,ite_false,Expr.inputEnd,
      max_le_iff,Nat.zero_le,updated,h.mode,prev,bound,held,h.half,true_and,and_true] <;>
    simp only [h.ballot.stock i, and_true]

private theorem bought (j : Fin 7) : (buyFields L B j).inputEnd≤cut := by
  fin_cases j
  · exact h.purchase.group
  · exact h.purchase.endpoint
  · exact h.purchase.opposite
  · exact max_le (Nat.zero_le _) (Nat.zero_le _)
  · exact Nat.zero_le _
  · exact h.purchase.length
  · exact max_le (max_le h.buy (Nat.zero_le _)) (max_le (Nat.zero_le _) h.menu)

theorem inputs (p : Pass) (listed : p∈writes L B) : p.term.inputEnd≤cut := by
  simp only [writes,List.mem_cons,List.mem_append] at listed
  rcases listed with rfl|rfl|rfl|((report|purchase)|stocks|quotes)
  · exact h.ballot.packet
  · exact h.buy
  · exact h.mode
  · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp report
    exact h.ballot.fields _ _ h.link.group h.link.endpoint h.link.opposite h.link.length h.printed j
  · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp purchase
    exact h.bought j
  · obtain ⟨ps,hps,hp⟩:=List.mem_flatten.mp stocks
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hps
    have ends:=h.endStock i
    simp only [stockWrites,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl
    · exact ends.1
    · exact ends.2.1
    · exact ends.2.2
  · obtain ⟨i,rfl⟩:=List.mem_ofFn.mp quotes
    apply h.ballot.quotes
    exact List.getElem_mem ..

end SnapshotReads

theorem placed_board (L : Dispatch) (B : Repair q d) (first bits w : ℕ)
    (h : SnapshotReads L (Calendar.PostLayout.place L B first bits) (first+2^bits))
    (keys : first+2^bits<2^w) : Board L (Calendar.PostLayout.place L B first bits) w :=
  Calendar.PostLayout.board L B first bits w h.inputs keys

end Hierarchy.ProtocolRAM.PurchaseStage

end OAI
