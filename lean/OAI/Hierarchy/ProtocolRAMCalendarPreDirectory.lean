import OAI.Hierarchy.ProtocolRAMCalendarStockTables

namespace OAI
/-! # Mounting signed-scatter row ordinals before running the priced commit -/

noncomputable section
open scoped Fin.CommRing
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM PurchaseStage StockCommit
open ThreeFlat.RAM
open scoped Classical

/-- After the guard, market, tests and post audit, original header cells still have their
entry values. This is used to establish the commit's own readiness. -/
theorem before_commit_cell {w q goods : ℕ} (C : Chart w q goods) (a : Attempt) (m : Memory w) (x : ℕ)
    (fr : (C.frozen a).ready ((guard C a).apply m))
    (ok : AuditReady (audits (C.layout a) (repair C a))
      (postSnapshot (C.layout a) (repair C a) (prepared C a m))) (safe : protected C x (.attempt a)) :
    postOutput (C.layout a) (repair C a) (prepared C a m) x=m x := by
  let B:=repair C a
  let L:=C.layout a
  rcases safe with ⟨hg,hf,hx,hy,hz,hm,ha,hv,_⟩
  change verdictMemory B.verdict (audits L B) (postSnapshot L B (prepared C a m)) x=m x
  have outside : ¬ (B.verdict ≤ x ∧ x < B.verdict + 1) := fun cell => (Nat.not_le.mpr hv) cell.1
  simp only [verdictMemory,image,fillSegment,ite_eq_right outside]
  rw [audit_below _ _ ok x ha]
  change postSnapshot L B (prepared C a m) x=m x
  have notMask : ¬ (B.repairBits.base ≤ x ∧ x < B.repairBits.base + L.candidates) :=
    fun cell => (Nat.not_le.mpr hm) cell.1
  simp only [postSnapshot,image,fillSegment,ite_eq_right notMask,AttemptGate.TestBoard.after]
  rw [B.tests.discrepancy.frame _ x hz,B.tests.payload.frame _ x hy,B.tests.excess.frame _ x hx]
  change (C.frozen a).after ((guard C a).apply m) x=m x
  rw [(C.frozen a).frame _ _ fr hf]
  simp [guard,Pass.apply,image,fillSegment,not_le.mpr hg]

/-- The parity and row reads of every sparse store are provided by the authentically
mounted occurrence header, including on failing privately supplied counters. -/
theorem Format.commit_ports {w z d k q goods : ℕ} (p : Format z d k q goods) (head : ℕ) (m : Memory w)
    (sealed : p.withOccurrenceHeader head=p) (count : p.occurrences=(p.occurrenceHeader head).count)
    (loaded : (p.occurrenceHeader head).Loaded m) :
    let s:=p.stockSource
    let h:=p.occurrenceHeader head
    s.owner.base+s.owner.size≤h.stop ∧ s.parity.base+s.parity.size≤h.stop ∧
    RepairHistogram.PairDirectory (p.pricedArea.columns s) m p.pricedArea.occurrences := by
  intro s h
  have owner : s.owner=h.owner :=
    (congrArg (fun f=>Format.stockSource f |>.owner) sealed).symm
  have parity : s.parity=h.parity :=
    (congrArg (fun f=>Format.stockSource f |>.parity) sealed).symm
  have right : h.parity.base+h.parity.size=h.stop := rfl
  have next : h.owner.base+h.owner.size=h.parity.base := rfl
  refine ⟨by rw [owner,next,←right];exact Nat.le_add_right ..,by rw [parity,right],?_⟩
  have len : p.pricedArea.occurrences=h.count := count
  rw [len]
  refine ⟨?_,?_,?_,?_⟩
  · change ∀i : Fin h.count,s.parity.read m _=0
    rw [parity]
    exact loaded.pair.first
  · change ∀i : Fin h.count,s.parity.read m _≠0
    rw [parity]
    exact loaded.pair.second
  · change ∀i : Fin h.count,s.owner.read m _=(i.val:Word w)
    rw [owner]
    exact loaded.pair.firstRow
  · change ∀i : Fin h.count,s.owner.read m _=(i.val:Word w)
    rw [owner]
    exact loaded.pair.secondRow

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
