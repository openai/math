import OAI.Hierarchy.ProtocolRAMPaidCheckoutRows
import OAI.Hierarchy.ProtocolRAMPaidProductFits
import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices

namespace OAI
/-! # Checkout preserves each original transaction at its actual occupied row -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.PaidCheckout
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe PaidWidths StockCommit
open ThreeFlat.RAM
open scoped Classical Fin.CommRing

theorem attempt {W z d k q goods r edges : ℕ} (f : Format z d k q goods) (sink : Sink r edges)
    (idBase : ℕ) (role : Expr) (ids : Fin goods→Expr) (tree core : Traversals) (bits flag : ℕ)
    (left right : Memory W) (low : PrefixAgreement.Low flag left right) (e : Fin edges)
    (old : (f.labelSource sink idBase role ids).edge.Fits W flag ∧ tree.edge.Fits W flag ∧
      tree.sourceRow.Fits W flag ∧ ∀ mask mate,tree.catalystMate=some (mask,mate)→
      mask.Fits W flag ∧ mate.Fits W flag)
    (path : core.edge.Fits W flag ∧ core.sourceRow.Fits W flag)
    (saved : (archivedBank f.pricedArea.direct f.pricedArea.occurrences).Fits W flag ∧
      (archivedBank f.pricedArea.broadcast f.pricedArea.rows).Fits W flag)
    (endAt : f.pricedArea.stop≤flag)
    (hits : ∀ i : Fin core.positions,(core.sourceRow.eval left (i.val:Word W)).val < f.pricedArea.goods) :
    ∀ s∈f.paidSlices sink idBase role ids tree core bits, s.load left e=s.load right e := by
  have same (s : Slice) (edge : s.edge.Fits W flag) (amount : s.amount.Fits W flag) :
      s.load left e=s.load right e :=
    load_congr s left right e
      (fun i=>PrefixAgreement.expr s.edge left right flag (PrefixAgreement.inputEnd_of_fits s.edge edge) low _)
      (fun i=>PrefixAgreement.expr s.amount left right flag (PrefixAgreement.inputEnd_of_fits s.amount amount) low _)
  have direct := same (paidDirect f.pricedArea f.stockSource (f.labelSource sink idBase role ids)) old.1 ⟨saved.1,trivial⟩
  have broad := same (paidBroadcast f.pricedArea tree.positions tree.owner tree.parity tree.edge tree.sourceRow
    f.board.batch.copies bits) old.2.1 (PaidAmount.product_fits bits (.lit _) (.lookup _ tree.sourceRow)
      trivial ⟨saved.2,old.2.2.1⟩)
  have spill : (paidSpill f.pricedArea core.positions core.owner core.parity core.edge core.sourceRow).load left e=
      (paidSpill f.pricedArea core.positions core.owner core.parity core.edge core.sourceRow).load right e := by
    apply load_congr
    · intro i
      exact PrefixAgreement.expr core.edge left right flag (PrefixAgreement.inputEnd_of_fits _ path.1) low _
    · intro i
      apply lookup_congr_at _ _ flag core.sourceRow left right _ path.2 low (hits i)
      change f.pricedArea.output+3*f.pricedArea.goods≤flag at endAt
      omega
  intro s entry
  cases hm : tree.catalystMate with
  | none =>
    simp [Format.paidSlices,Format.mateSlices,hm] at entry
    rcases entry with rfl|rfl|rfl
    · exact direct
    · exact broad
    · exact spill
  | some t =>
    simp [Format.paidSlices,Format.mateSlices,hm] at entry
    rcases entry with rfl|rfl|rfl|rfl
    · exact direct
    · have mate:=old.2.2.2 t.1 t.2 hm
      exact same _ mate.2 ⟨mate.1,trivial,trivial,saved.1,trivial⟩
    · exact broad
    · exact spill

theorem feed {W edges : ℕ} (c : CommodityColumn) (t : Traversals) (flag : ℕ)
    (left right : Memory W) (low : PrefixAgreement.Low flag left right) (e : Fin edges)
    (path : t.edge.Fits W flag ∧ t.sourceRow.Fits W flag) (endAt : c.overflow+c.rows≤flag)
    (hits : ∀i : Fin t.positions,(t.sourceRow.eval left (i.val:Word W)).val<c.rows) :
    (c.paidSlice t).load left e=(c.paidSlice t).load right e :=
  load_congr (c.paidSlice t) left right e
    (fun _i=>PrefixAgreement.expr t.edge left right flag (PrefixAgreement.inputEnd_of_fits _ path.1) low _)
    (fun i=>lookup_congr_at c.overflow c.rows flag t.sourceRow left right _ path.2 low (hits i) endAt)

end Hierarchy.ProtocolRAM.Calendar.PaidCheckout
end

end OAI
