import OAI.Hierarchy.ProbePaidStripHits
import OAI.Hierarchy.ProtocolRAMCatalystArchiveChronology
import OAI.Hierarchy.ProtocolRAMCalendarOccurrenceFormat

namespace OAI
/-! # Native width bounds for the direct, second-radius and selector slices -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe Calendar Calendar.StockCommit RepairHistogram PurchaseStage
open scoped Classical Fin.CommRing BigOperators
variable {w d q edges : ℕ}

theorem chooseField_value_le (n base : ℕ) (fields : Fin n→Expr) (index : Expr)
    (m : Memory w) (r : Word w) (cap : ℕ) (small : ∀i,((fields i).eval m r).val≤cap) :
    ((chooseField n base fields index).eval m r).val≤cap := by
  induction n generalizing base with
  | zero => simp [chooseField,Expr.eval]
  | succ n ih =>
    rw [chooseField,Expr.eval]
    split
    · exact small 0
    · exact ih _ _ (fun i=>small i.succ)

/-- The finite paid-wire selector is capped even when a role falls outside the
padded board. Its default is zero and every real branch is a validated batch. -/
theorem Calendar.Format.sealed_installation_bound {z D k : ℕ} (f : Format z D k q d) (start : ℕ)
    (closed : f.withOccurrenceHeader start=f) (m : Memory w) (i : Fin f.occurrences)
    (term : q≤2^w) (copies : f.board.batch.copies<2^w) (sum : q*f.board.batch.copies<2^w) :
    installedBits (fresh f.pricedArea f.stockSource).columns m i≤f.board.batch.maxWidth*f.board.batch.copies := by
  let h:=f.occurrenceHeader start
  let b:=enabledBatch f.market.layout f.board
  change (f.stockSource.credit.eval m (i.val:Word w)).val≤_
  have code : f.stockSource.credit=(f.withOccurrenceHeader start).stockSource.credit := by rw [closed]
  rw [code]
  change ((chooseField d 0 (fun j=>(b.wire (f.board.wire j)).atRow h.ballTerm) h.fieldTerm).eval m
    (i.val:Word w)).val≤_
  apply chooseField_value_le
  intro j
  rw [eval_atRow]
  exact b.wire_bound m _ _ term copies sum

/-- The ordinary debit column is read from its actual chronological commit.
The case split is the native ordinary-resource test used by the first pass. -/
theorem CatalystArchive.priced_installation (C : Chart w q d) (e : Attempt) (m : Memory w)
    (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d)
    (physical : C.commit e=pricedSegment a s g w b) (mounted : ready C (.attempt e) m)
    (board : EventBoard (fresh a s) w) (j : Fin a.occurrences) :
    let st:=fresh a s
    let v:=postOutput (C.layout e) (repair C e) (prepared C e m)
    let u:=stageInput a s g v
    (after C (.attempt e) m (a.direct+j.val)).val=
      if kind (goods:=a.goods) st.plan.bank st.columns u j=none then installedBits st.columns u j else 0 := by
  intro st v u
  obtain ⟨_,_,_,_,_,_,_,_,_,_,commitReady,_,_⟩:=mounted
  rw [physical] at commitReady
  rw [Calendar.after,physical,StockCommit.priced_after]
  have ok : (st.native w a.rows b).ready u:=commitReady.2.2
  exact (st.read_direct b u j ok board.chargeFits board.order (board.hit b u ok j) board.bound (board.keep j)).1

theorem PaidWidths.Slice.load_le_cells (s : PaidWidths.Slice) (m : Memory w) (e : Fin edges) (cap : ℕ)
    (small : ∀i : Fin s.count,(s.amount.eval m (i.val:Word w)).val≤cap) : s.load m e≤ s.count*cap := by
  unfold PaidWidths.Slice.load
  calc
    _ ≤ ∑ _ : Fin s.count,cap := Finset.sum_le_sum (fun i _=>by split <;> first | exact small i | omega)
    _ = _ := by simp

theorem PaidWidths.broadcast_load_bound (a : Area) (n : ℕ) (owner parity : Bank) (edge ball : Expr)
    (copies maxBits : ℕ) (m : Memory w) (e : Fin edges) :
    (PaidWidths.paidBroadcast a n owner parity edge ball copies maxBits).load m e≤n*(maxBits*copies) := by
  apply PaidWidths.Slice.load_le_cells
  intro i
  have h:=boundedMul_value_le m (i.val:Word w) maxBits (.lit copies)
    (.lookup (PaidWidths.archivedBank a.broadcast a.rows) ball)
  exact h.trans (Nat.mul_le_mul_left _ (Nat.mod_le _ _))

end Hierarchy.ProtocolRAM
end

end OAI
