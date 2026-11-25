import OAI.Hierarchy.ProtocolRAMCalendarStockStepBound

namespace OAI
/-! # Physical mode and purchase fields at a selected native repair -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM PurchaseStage
open ThreeFlat.RAM
open scoped Fin.CommRing
variable {w q d : ℕ}

/-- A mode-two repair records zero in every buy slot, including unselected
padding, on the actual output of the entire priced stage. -/
theorem failure_flags (C : Chart w q d) (a : Attempt) (entry : Memory w)
    (mounted : ready C (.attempt a) entry) (board : Board (C.layout a) (repair C a) w)
    (wide : 4≤2^w)
    (failed : AttemptGate.actual (repair C a).policy
      (postSnapshot (C.layout a) (repair C a) (prepared C a entry))=2) (i : Fin (C.layout a).candidates) :
    after C (.attempt a) entry ((repair C a).purchaseOut+i.val)=0 := by
  let B:=repair C a
  let L:=C.layout a
  let m:=postSnapshot L B (prepared C a entry)
  let flag : Pass:=⟨B.purchaseOut,L.candidates,buyWord L B⟩
  have read:=attempt_read C a entry mounted board flag (List.mem_cons_of_mem _ (List.mem_cons_self ..)) i
  change after C (.attempt a) entry (B.purchaseOut+i.val)=(buyWord L B).eval m (i.val:Word w) at read
  rw [read]
  change (AttemptGate.ifMode B.policy 3 _ _).eval m (i.val:Word w)=0
  rw [AttemptGate.ifMode_eval _ _ _ _ _ _ wide (by decide)]
  change AttemptGate.actual B.policy m=2 at failed
  rw [ite_eq_right (by omega)]
  rfl

/-- Every transactional stock row reads the exact failure mode at the same
snapshot that determines its native histogram. -/
theorem failure_mode (C : Chart w q d) (a : Attempt) (entry : Memory w)
    (A : Area) (s : Sources) (g : LabelSource) (budget : ℕ)
    (mounted : ready C (.attempt a) entry) (board : Board (C.layout a) (repair C a) w)
    (positive : 0<(C.layout a).candidates)
    (window : StockWindow A s g (C.modeAt a) budget w)
    (failed : AttemptGate.actual (repair C a).policy
      (postSnapshot (C.layout a) (repair C a) (prepared C a entry))=2) (i : Fin A.goods) :
    let B:=repair C a
    let L:=C.layout a
    let post:=postOutput L B (prepared C a entry)
    let b:=enabledBatch L B
    (s.mode.eval (pricedTransfer A s g b post) (i.val:Word w)).val=2 := by
  intro B L post b
  let u:=prepared C a entry
  let snap:=postSnapshot L B u
  let row : Fin L.candidates:=⟨0,positive⟩
  let mode : Pass:=⟨B.modeOut,L.candidates,AttemptGate.mode B.policy⟩
  obtain ⟨_,_,_,_,_,_,checks,_,_,_,_,_,_⟩:=mounted
  have read:=post_read L B u checks board mode
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) row
  have stamp : post (C.modeAt a)=(AttemptGate.actual B.policy snap:Word w):=read.trans (AttemptGate.mode_eval ..)
  rw [window.mode,word_eval,pricedTransfer_prior A s g b post window.room window.label _ window.modeBefore,
    stamp,Fin.val_cast_of_lt ((AttemptGate.actual_lt ..).trans_le window.wide)]
  exact failed

end Hierarchy.ProtocolRAM.Calendar.StockCommit
end

end OAI
