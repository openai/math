import OAI.Hierarchy.ProtocolRAMCalendarReportedPriceRows
import OAI.Hierarchy.ProtocolRAMCalendarSignedHistory

namespace OAI
/-! # Positive installed-width bill, opening fees and released catalyst bits in one native event -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram PurchaseStage AdaptiveProbe
open scoped BigOperators Classical
noncomputable section
variable {w q d : ℕ}

/-- Read the five signed event columns, all from the *terminal* physical archive.
Positive installation and negative catalyst ownership have their original, distinct
addresses. The activation bill is charged once per emitted buy flag. -/
def charges (B : CashColumns) (n rows goods paths : ℕ) (m : Memory w) (payload copies : ℕ)
    (cost : Fin n→ℝ) (tree : Fin rows→ℝ) (route : Fin goods→ℝ) (opening : Fin paths→ℝ) : Charges :=
  ⟨(∑i : Fin n,((m (B.direct+i.val)).val:ℝ)*cost i)/payload+
    (∑j : Fin rows,(copies:ℝ)*(tree j*(m (B.broadcast+j.val)).val))/payload+
    ∑i : Fin goods,((m (B.excess+i.val)).val:ℝ)/payload*route i,
   ∑j : Fin paths,((m (B.buy+j.val)).val:ℝ)*opening j,
   ∑i : Fin n,(m (B.direct+n+i.val)).val⟩

/-- An active direct purchase is priced at its actual emitted physical edge length,
and withdrawn external catalyst bits are priced at their two radius links. Zero
rows may carry any padded key. -/
theorem charges_bill (B : CashColumns) (n rows goods paths : ℕ) (m : Memory w) (payload copies M : ℕ)
    (positive : 0<payload) (price cost : Fin n→ℝ) (tree : Fin rows→ℝ) (route : Fin goods→ℝ)
    (opening : Fin paths→ℝ) (in_cost : ∀i,(m (B.direct+i.val)).val≠0→price i=cost i)
    (out_cost : ∀i,(m (B.direct+n+i.val)).val≠0→price i=2*M) :
    eventBill B m payload copies price tree route opening=(charges B n rows goods paths m payload copies cost tree route opening).net M payload := by
  have hw : (payload:ℝ)≠0 := by exact_mod_cast positive.ne'
  have credit (i : Fin n) : ((m (B.direct+i.val)).val:ℝ)*price i/payload=((m (B.direct+i.val)).val:ℝ)*cost i/payload := by
    by_cases h : (m (B.direct+i.val)).val=0
    · simp [h]
    · rw [in_cost i h]
  have debit (i : Fin n) : ((m (B.direct+n+i.val)).val:ℝ)*(-price i)/payload=
      -(2*(M:ℝ)*((m (B.direct+n+i.val)).val:ℝ)/payload) := by
    by_cases h : (m (B.direct+n+i.val)).val=0
    · simp [h]
    · rw [out_cost i h]
      ring
  have fee (i : Fin paths) : ((m (B.buy+i.val)).val:ℝ)*(payload*opening i)/payload=
      ((m (B.buy+i.val)).val:ℝ)*opening i := by field_simp
  have broadcast (i : Fin rows) : ((m (B.broadcast+i.val)).val:ℝ)*(copies*tree i)/payload=
      (copies:ℝ)*(tree i*(m (B.broadcast+i.val)).val)/payload := by ring
  have core (i : Fin goods) : ((m (B.excess+i.val)).val:ℝ)*route i/payload=
      ((m (B.excess+i.val)).val:ℝ)/payload*route i := by ring
  simp only [eventBill,Fintype.sum_sum_type,CashColumns.addr,eventPrice,credit,debit,fee,broadcast,core,
    charges,Charges.net,Finset.sum_div,Finset.sum_neg_distrib,Nat.cast_sum,Finset.mul_sum]
  ring

theorem reportedRows_bill (a : StockCommit.Area) (s : StockCommit.Sources) (g : StockCommit.LabelSource)
    (B : Repair q d) (routeKey : Fin a.goods→ℕ) (payload copies M : ℕ)
    (link : Fin a.occurrences→ℕ→ℝ) (tree : Fin a.rows→ℕ→ℝ) (core : Fin a.goods→ℕ→ℝ)
    (fee : Fin a.rows→ℕ→ℝ) (m : Memory w) (cost : Fin a.occurrences→ℝ) (wp : 0<payload)
    (install : ∀i,(m (a.direct+i.val)).val≠0→link i (m (g.out+i.val)).val=cost i)
    (release : ∀i,(m (a.direct+a.occurrences+i.val)).val≠0→link i (m (g.out+i.val)).val=2*M) :
    let cols := (StockCommit.fresh a s).eventColumns B.purchaseOut
    let bill := charges cols a.occurrences a.rows a.goods a.rows m payload copies cost
      (fun j=>tree j (m (B.reportOut 6+j.val)).val) (fun i=>core i (m (routeKey i)).val)
      (fun j=>fee j (m (B.boughtFields 5+j.val)).val)
    (reportedRows a s g B routeKey payload copies link tree core fee).bill payload m=bill.net M payload := by
  intro cols bill
  rw [reportedRows, WordRows.bill_ports]
  have keyed := (StockCommit.fresh a s).event_value B.purchaseOut payload copies m
    (StockCommit.reportedKeys a g B routeKey) link tree core fee
  exact keyed.trans (charges_bill cols _ _ _ _ m payload copies M wp _ cost _ _ _ install release)

/-- A feed contributes its actual charged overflow alone and is independent
of repair, stopping, or warm replay flags. -/
theorem spillRows_bill {z N k : ℕ} (l : FeedLayout z N k) (key : FeedLayout.Good z N k→ℕ)
    (price : FeedLayout.Good z N k→ℕ→ℝ) (m : Memory w) (payload M : ℕ) :
    let cost := ∑i : FeedLayout.Good z N k,((m (l.overflow+PurchaseInventory.slot i)).val:ℝ)*
      price i (m (key i)).val/payload
    (spillRows l key price).bill payload m=(⟨cost,0,0⟩ : Charges).net M payload := by
  simp only [spillRows,WordRows.bill_ports,ChargeWord.value,Charges.net,Nat.cast_zero,mul_zero,zero_div,
    sub_zero,add_zero]

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
