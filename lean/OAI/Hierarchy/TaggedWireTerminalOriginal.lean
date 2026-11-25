import OAI.Hierarchy.TaggedWireHistorySockets
import OAI.Hierarchy.TaggedWidePrivateOrdinals
import OAI.Hierarchy.ProtocolRAMCatalogueAlignment
import OAI.Hierarchy.TaggedWideReportGrouping

namespace OAI
/-! # Original private and paid socket ordinals of every live native terminal word -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment
open ProbeStage CoreBoard AdaptiveProbe ReportSockets Tagged Tagged.WideStack
open TaggedShorterSupergroups TaggedShorterFields TaggedShorterBudget ProtocolRAMEmit ProtocolRAMReportedPorts
open scoped Classical
variable {h W k attempts M : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marked : Marks h W k attempts) (unique : Exclusive marked)
    (b : Board) (order : Fin b.coreRows≃Edges S h (2^W) k) (acquired : Bought S π depth marked→Fin b.boughtRows)
    (raw : Fin b.rows→ProtocolRAMEmit.Row)
local notation "name" => b.original S π depth marked order acquired
local notation "label" => HistoryRoles.labelled S π depth marked
variable (receipt : Alignment b S π depth marked M raw (fun i=>(raw i).width)
    (b.original S π depth marked order acquired))
abbrev Active := {i : Fin b.rows // 0<(raw i).width}

/-- The native catalogue partition and original socket partition commute
on every observed row. Vacant paid acquisitions cannot enter this domain. -/
theorem partition_original (i : Active b raw) :
    b.partition order i.val=Sum.map id (Sum.map id acquired) (label (receipt.ident i)) := by
  rw [← receipt.original i]
  cases q:receipt.ident i with
  | inl x=>rcases x with f|⟨⟨a,t⟩,l⟩
           · exact b.private_row order f
           · exact b.positive_core_row order ((t,a),l)
  | inr e=>exact b.bought_row order (acquired e)

/-- The actual orientation flip used by the role ROM. The mathematical
chord and its source bits are always ordered by the same physical site words. -/
def sourceSide (i : Active b raw) (s : Bool) :=
  HistoryRoles.swap S π depth marked (.inl (receipt.ident i)) s

def originalPort (i : Active b raw) (s : Bool) : HistoryRoles.Public S h W k attempts :=
  .inl (HistoryRoles.paid S π depth marked unique (receipt.ident i,sourceSide S π depth marked b order acquired raw receipt i s))

variable {H : ℕ} (dir : Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H)

theorem private_original (i : Active b raw) (dormant : ¬b.transport order i.val) (s : Bool) :
    let f:=(b.freeOrdinal order).symm ⟨i.val,dormant⟩
    originalPort S π depth marked unique b order acquired raw receipt i s=
      .inl (.inl (f,sourceSide S π depth marked b order acquired raw receipt i s)) := by
  intro f
  have row:(b.freeOrdinal order f).val=i.val:=
    congrArg Subtype.val ((b.freeOrdinal order).apply_symm_apply ⟨i.val,dormant⟩)
  have ri : b.partition order i.val=.inl f:=
    (congrArg (b.partition order) row.symm).trans (b.private_row order f)
  have classified := partition_original S π depth marked b order acquired raw receipt i
  rw [ri] at classified
  have code : label (receipt.ident i)=.inl f := by
    rcases found:label (receipt.ident i) with a|z
    · simpa [found] using classified.symm
    · simp [found] at classified
  change Sum.inl (HistoryRoles.paid S π depth marked unique (receipt.ident i,_))=_
  unfold HistoryRoles.paid
  simp [Equiv.sumProdDistrib,code]

private theorem exists_positive_row (i : {i : Active b raw // b.transport order i.val}) :
    ∃ r, label (receipt.ident i.val) = .inr r := by
  rcases eq:label (receipt.ident i.val) with f|r
  · have hi := partition_original S π depth marked b order acquired raw receipt i.val
    rw [eq] at hi
    have active := i.property
    simp [Board.transport,hi] at active
  · exact ⟨r,rfl⟩

/-- Positive-width transport roles are the original marked/bought report row.
Consequently their actual public endpoints are the corresponding fixed packed
stage slots, regardless of how the positive sublist is numbered. -/
def positiveRow (i : {i : Active b raw // b.transport order i.val}) : ReportSockets.Row S π depth marked :=
  (exists_positive_row S π depth marked b order acquired raw receipt i).choose

theorem positive_spec (i : {i : Active b raw // b.transport order i.val}) :
    label (receipt.ident i.val)=.inr (positiveRow S π depth marked b order acquired raw receipt i) :=
  (exists_positive_row S π depth marked b order acquired raw receipt i).choose_spec

def positiveRows : {i : Active b raw // b.transport order i.val} ↪ ReportSockets.Row S π depth marked where
  toFun:=positiveRow S π depth marked b order acquired raw receipt
  inj' := by
    intro i j eq
    have hi:=positive_spec S π depth marked b order acquired raw receipt i
    have hj:=positive_spec S π depth marked b order acquired raw receipt j
    exact Subtype.ext (receipt.ident.injective ((label).injective ((hi.trans (congrArg Sum.inr eq)).trans hj.symm)))

theorem positive_original (i : {i : Active b raw // b.transport order i.val}) (s : Bool) :
    originalPort S π depth marked unique b order acquired raw receipt i.val s=
      .inl (.inr (locate S π depth marked unique (positiveRow S π depth marked b order acquired raw receipt i,
        sourceSide S π depth marked b order acquired raw receipt i.val s))) := by
  unfold originalPort HistoryRoles.paid
  simp [Equiv.sumProdDistrib,positive_spec]

theorem positive_packed_site (i : {i : Active b raw // b.transport order i.val}) (s : Bool) :
    publicSite dir (packed dir (locate S π depth marked unique
      (positiveRow S π depth marked b order acquired raw receipt i,
       sourceSide S π depth marked b order acquired raw receipt i.val s)))=
    some (ReportSockets.geometry S π depth marked
      (positiveRow S π depth marked b order acquired raw receipt i)
      (sourceSide S π depth marked b order acquired raw receipt i.val s)) :=
  actual_site (dir:=dir) (S:=S) (π:=π) (depth:=depth) (marked:=marked) (unique:=unique) _ _

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment

end
end OAI
