import OAI.Hierarchy.ProtocolRAMCatalogueAlignment
import OAI.Hierarchy.TaggedWidePrivateOrdinals

namespace OAI
/-! # The native terminal pruning geometry and its fixed public positive ordinals -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open AdaptiveProbe ProbeStage CoreBoard ReportSockets ProtocolRAMEmit
open scoped Classical
variable {h W k attempts M depth : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {b : Board} {marks : Marks h W k attempts} {rows : Fin b.rows→ProtocolRAMEmit.Row}
    {name : Catalogue S π depth marks→Fin b.rows}
    (a : Alignment b S π depth marks M rows (fun i=>(rows i).width) name)

def Alignment.rowFlip (i : ActiveRows rows) := decide
  ((rows i.val).endpoint≠(siteNumber h (2^W) k (actualEnds S π depth marks (a.ident i)).1).val)

theorem Alignment.ends_at (i : ActiveRows rows) :
    let z:=actualEnds S π depth marks (a.ident i)
    (rows i.val).endpoint=(siteNumber h (2^W) k (if a.rowFlip i then z.2 else z.1)).val ∧
    (rows i.val).opposite=(siteNumber h (2^W) k (if a.rowFlip i then z.1 else z.2)).val := by
  let z:=actualEnds S π depth marks (a.ident i)
  have distinct : (siteNumber h (2^W) k z.2).val≠(siteNumber h (2^W) k z.1).val :=
    fun eq=>actual_distinct S π depth marks (a.ident i) ((siteNumber h (2^W) k).injective (Fin.ext eq.symm))
  rcases a.joins i with direct|reverse
  · simp [Alignment.rowFlip,direct.1,direct.2]
  · have no : (rows i.val).endpoint≠(siteNumber h (2^W) k z.1).val:=by rw [reverse.1]; exact distinct
    change (rows i.val).endpoint=(siteNumber h (2^W) k (if a.rowFlip i then z.2 else z.1)).val ∧
      (rows i.val).opposite=(siteNumber h (2^W) k (if a.rowFlip i then z.1 else z.2)).val
    have yes : a.rowFlip i=true:=by simpa [Alignment.rowFlip] using no
    simpa [yes] using reverse

def Alignment.geometry (w R : ℕ) : Geometry (boardLayout h (2^W) k w R) M 1 rows :=
  pruning S π depth marks w R M rows a.ident a.rowFlip a.ends_at a.metric

theorem Alignment.scale_read (w R : ℕ) (i : ActiveRows rows) :
    (a.geometry w R).scale i=scaleOf S π depth marks (a.ident i) := rfl

theorem Alignment.transport_iff (order : Fin b.coreRows≃Edges S h (2^W) k)
    (acq : Bought S π depth marks→Fin b.boughtRows)
    (orig : ∀e,name e=b.original S π depth marks order acq e)
    (i : ActiveRows rows) : b.transport order i.val ↔ 0<scaleOf S π depth marks (a.ident i) := by
  have atRow : i.val=b.original S π depth marks order acq (a.ident i):=(a.original i).symm.trans (orig _)
  unfold Board.transport
  rw [atRow]
  rcases hEdge:a.ident i with (f|⟨⟨j,t⟩,l⟩)|r
  · rw [show b.partition order (b.original S π depth marks order acq (.inl (.inl f)))=.inl f from b.private_row order f]
    simp [scaleOf,coreScale]
  · rw [show b.partition order (b.original S π depth marks order acq (.inl (.inr ((j,t),l))))=.inr (.inl ((t,j),l)) from b.positive_core_row order ((t,j),l)]
    simp [scaleOf,coreScale,dyadicScale]
  · rw [show b.partition order (b.original S π depth marks order acq (.inr r))=.inr (.inr (acq r)) from b.bought_row order (acq r)]
    simp [scaleOf,dyadicScale]

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI
