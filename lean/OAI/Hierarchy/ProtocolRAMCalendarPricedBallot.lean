import OAI.Hierarchy.ProtocolRAMCalendarStockStepBound
import OAI.Hierarchy.ProtocolRAMStockPortPlan

namespace OAI
/-! # The elected row set survives the physical audit, label and stock preambles -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM PurchaseStage RepairHistogram StockCommit
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {w q d : ℕ}

private theorem refit_no (n : ℕ) (need stock : Fin n→Expr) (yes old new : Expr) (cut : ℕ)
    (h : (ifEnough n need stock yes old).Fits w cut) (replacement : new.Fits w cut) :
    (ifEnough n need stock yes new).Fits w cut := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact ⟨h.1,h.2.1,replacement,ih _ _ h.2.2.2⟩

/-- The native validator returns zero precisely on rows that contribute to the
multiplicity and charge sums. The other rows all return one. -/
def committedKey (b : Batch q d) := b.ifSelected (b.ifPacket (.lit 0) (.lit 1)) (.lit 1)

theorem committedKey_read (b : Batch q d) (m : Memory w) (r : Word w)
    (wide : 1<2^w) (letters : q≤2^w) (copies : b.copies<2^w) (total : q*b.copies<2^w) :
    (committedKey b).eval m r=0 ↔ committed b m r := by
  have one : (1:Word w)≠0 := by
    intro h
    have impossible:=congrArg Fin.val h
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt wide] at impossible
    exact Nat.one_ne_zero impossible
  rw [committedKey,Batch.eval_ifSelected,Batch.eval_ifPacket _ _ _ _ _ letters copies total]
  by_cases active : b.selected m r <;> by_cases valid : b.withinPacket m r ∧ (∑i,((b.field i).eval m r).val)=b.copies <;>
    simp [active,valid,committed,Expr.eval,one]

private theorem committedKey_fit (b : Batch q d) (cut : ℕ) (ok : (invalidExpr b).Fits w cut) :
    (committedKey b).Fits w cut := by
  exact ⟨ok.1,ok.2.1,trivial,ok.2.2.2.1,ok.2.2.2.2.1,trivial,
    refit_no d b.need b.stock (b.ifPacket (.lit 0) (.lit 1)) _ (.lit 1) cut ok.2.2.2.2.2.2 trivial⟩

/-- The admission pass itself supplies the footprint of the selected histogram
expression; no extra agreement of the priced and unpriced rows is required. -/
theorem priced_liveRows (L : Dispatch) (B : Repair q d) (A : Area) (s : Sources) (g : LabelSource)
    (m : Memory w) (plan : AuditReady (audits L B) (postSnapshot L B m))
    (ordered : OrderedTallies (audits L B)) (wide : 1<2^w)
    (endFlag : B.keys≤B.verdict) (stamp : B.keys≤g.out) (seed : g.out≤A.start) :
    liveRows (enabledBatch L B) (stageInput A s g (postOutput L B m)) L.candidates =
      liveRows (enabledBatch L B) (postSnapshot L B m) L.candidates := by
  let b:=enabledBatch L B
  have inspection : (PurchaseStage.inspection L B).Fits w:=plan.1
  obtain ⟨valid,typed,_,letters,copies,total⟩:=inspection
  have fit:=committedKey_fit b B.keys valid
  have checked (u : Audit) (hu : u∈audits L B) : B.keys≤u.low := by
    change u∈Audit.check (PurchaseStage.inspection L B)::columns (writes L B) at hu
    rcases List.mem_cons.mp hu with rfl|tail
    · exact le_rfl
    · have h:=ordered.1 u tail
      change B.tally+1<u.low at h
      change B.keys+L.candidates≤B.tally at typed
      omega
  ext i
  simp only [StockCommit.liveRows,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [←committedKey_read b _ _ wide letters copies total,←committedKey_read b (postSnapshot L B m) _ wide letters copies total,
    stage_input A s g _ _ _ (ProtocolRAMGeneratedWrite.fits_mono _ stamp fit) seed,
    post_input L B m _ _ B.keys plan fit checked endFlag]

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
