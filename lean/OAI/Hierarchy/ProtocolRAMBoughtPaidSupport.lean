import OAI.Hierarchy.ProtocolRAMBoughtCatalogueActual
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueFits
import OAI.Hierarchy.ProtocolRAMCalendarPaidReporter

namespace OAI
/-! # Original purchased edge rows at the final route reporter -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native CoreBoard PurchaseFrozen ReportSockets BoughtSockets
open ThreeFlat.RAM PhysicalProcedure CatalogueRows
open scoped Fin.CommRing Classical
noncomputable section
variable {w z W k attempts q goods r edges n count K H : ℕ}

theorem paid_after_run (C : Chart w q goods) (flag : ℕ) (sink : Sink r edges) (src : ℕ) (slices : List PaidWidths.Slice)
    (archive : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ) (m : Memory w)
    (limit : ℕ) (sources : ∀s∈slices,s.Fits sink.banks.width edges src w)
    (targets : limit≤flag ∧ limit ≤ sink.banks.width.base ∧ limit ≤ sink.banks.reserved.base ∧
      limit ≤ sink.banks.used.base ∧ limit≤archive.scratch) :
    ∀x<limit,paidSource C flag sink src slices archive reserve site debit m x=run C (events C.mesh) m x := by
  obtain ⟨h₀,h₁,h₂,h₃,h₄⟩:=targets
  intro x small
  rw [paidSource,ReserveUse.frame _ _ _ _ _ _ x (.inl (small.trans_le h₂)) (.inl (small.trans_le h₃))
    (.inl (small.trans_le h₄)),PaidWidths.frame _ _ _ _ _ x sources (small.trans_le h₁),checkedOut,
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (small.trans_le h₀))]

/-- `priced_catalogue` at the very same original row now consumed by the
native seven-field report, after actual payment and reserve settlement. -/
theorem paid_catalogue_of_run (C : Chart w q goods) (flag : ℕ) (sink : Sink r edges) (src : ℕ) (slices : List PaidWidths.Slice)
    (archive : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ) (m : Memory w)
    (limit : ℕ) (sources : ∀s∈slices,s.Fits sink.banks.width edges src w)
    (targets : limit≤flag ∧ limit ≤ sink.banks.width.base ∧ limit ≤ sink.banks.reserved.base ∧
      limit ≤ sink.banks.used.base ∧ limit≤archive.scratch)
    (v : BoughtSockets.Directory attempts) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth metric G : ℕ)
    (marks : Marks z W k attempts) :
    let x:=v.source S z W k depth K G H
    let h:=v.header z (2^W) k S.degree depth
    let before:=run C (events C.mesh) m
    let after:=paidSource C flag sink src slices archive reserve site debit m
    x.All (Expr.Fits w limit) →
    (∀j : Fin h.count,x.flag.eval before (j.val:Word w)≠0 ↔
      ∃p : Bought S π depth marks,h.enum ⟨p.1,BoughtLocation.relative p.2⟩=j ∧
        Located S π depth marks metric (x.view before (j.val:Word w)) (.inr p)) →
    ∀j : Fin h.count,x.flag.eval after (j.val:Word w)≠0 ↔
      ∃p : Bought S π depth marks,h.enum ⟨p.1,BoughtLocation.relative p.2⟩=j ∧
        Located S π depth marks metric (x.view after (j.val:Word w)) (.inr p) := by
  intro x h before after fit account j
  have same:=paid_after_run C flag sink src slices archive reserve site debit m limit sources targets
  obtain ⟨g,l,r,f,t⟩:=fit
  have read (e : Expr) (ok : e.Fits w limit) := eval_below e (j.val:Word w) before after ok same
  rw [read x.flag f]
  have view : x.view after (j.val:Word w)=x.view before (j.val:Word w) := by
    simp only [BoughtSource.view,read x.group g,read x.left l,read x.right r,read x.flag f,read x.menu t]
  simpa only [view] using account j

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
