import OAI.Hierarchy.TaggedWireWideSocketDirectory
import OAI.Hierarchy.ProtocolRAMCatalogueAlignment
import OAI.Hierarchy.ProtocolRAMCatalogueActiveBill

namespace OAI
/-! # The signed shelf and funded cut name the same original positive row -/

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

open AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows ProtocolRAMEmit
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

section Ordinals
set_option quotPrecheck false
variable (h width : ℕ)
local notation "D" => 2^v.W
local notation "P" => v.widePlacement h width
local notation "order" => v.wideOrder h width

/-- Public chronological candidate ordinal in the real rectangular archive. -/
theorem wide_dated_bought_rows : v.wideJobs*(PurchaseFrozen.count h D k*
    PurchaseFrozen.paths h v.sampler.degree v.depth)=(P).catalogue.boughtRows := rfl

variable (π : Equiv.Perm (Fin (2^h))) (marks : Marks h v.W k v.wideJobs)
local notation "bsize" => v.wide_dated_bought_rows h width
local notation "ordinal" => (P).catalogue.ordinal v.sampler π v.depth marks order bsize

theorem wide_dated_original_ordinal (a : Catalogue v.sampler π v.depth marks) :
    (P).catalogue.original v.sampler π v.depth marks order (v.wideBoughtOrdinal h width π marks) a=ordinal a := by
  cases a <;> rfl

end Ordinals

/-- At each positive physical row the immutable catalogue ordinal determines the edge
and its purchase date. Thus the entire alignment, including the orientation used by
the signed shelf, is unique. -/
theorem wide_sourceAlignment_unique (h width : ℕ) (π : Equiv.Perm (Fin (2^h)))
    (marks : Marks h v.W k v.wideJobs) (rows : Fin (v.widePlacement h width).catalogue.rows → Row)
    {M : ℕ} {fixed : Fin (v.widePlacement h width).catalogue.rows → ℕ}
    (left right : Alignment (v.widePlacement h width).catalogue v.sampler π v.depth marks M rows fixed
      ((v.widePlacement h width).catalogue.original v.sampler π v.depth marks (v.wideOrder h width)
        (v.wideBoughtOrdinal h width π marks))) :
    left = right := by
  have same : left.ident = right.ident := by
    apply Function.Embedding.ext
    intro i
    apply ((v.widePlacement h width).catalogue.ordinal v.sampler π v.depth marks
      (v.wideOrder h width) (v.wide_dated_bought_rows h width)).injective
    rw [← v.wide_dated_original_ordinal h width π marks (left.ident i),
        ← v.wide_dated_original_ordinal h width π marks (right.ident i)]
    exact (left.original i).trans (right.original i).symm
  cases left
  cases right
  cases same
  rfl


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end OAI
