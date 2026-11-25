import OAI.Hierarchy.ProtocolRAMCatalogueRowFields
import OAI.Hierarchy.ProbeReportedGeometry

namespace OAI
/-! # Original catalogue names and endpoints of positive emitted rows -/

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open ProbeStage CoreBoard ProbeStage.ReportSockets AdaptiveProbe ProtocolRAMEmit
noncomputable section
variable {h W k attempts : ℕ}

/-- A named edge has precisely one physical row even when different acquired
chains have the same geometric endpoints. -/
def Board.original (b : Board) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k attempts) (order : Fin b.coreRows≃Edges S h (2^W) k)
    (acquired : Bought S π depth marks→Fin b.boughtRows) : Catalogue S π depth marks→Fin b.rows :=
  Sum.elim (fun e=>b.coreIndex (order.symm e)) (fun e=>b.boughtIndex (acquired e))

/-- The full-width terminal row, restricted to those used by the fixed wires,
recovers the earlier immutable physical edge identifier. -/
structure Alignment (b : Board) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k attempts) (M : ℕ) (rows : Fin b.rows→Row)
    (fixed : Fin b.rows→ℕ) (name : Catalogue S π depth marks→Fin b.rows) where
  ident : {i : Fin b.rows // 0<fixed i} ↪ Catalogue S π depth marks
  original : ∀i,name (ident i)=i.val
  joins : ∀i,let ends:=actualEnds S π depth marks (ident i)
    let a:=(siteNumber h (2^W) k ends.1).val
    let z:=(siteNumber h (2^W) k ends.2).val
    ((rows i.val).endpoint=a ∧ (rows i.val).opposite=z) ∨ ((rows i.val).endpoint=z ∧ (rows i.val).opposite=a)
  metric : ∀i,(rows i.val).lengthCode=lenCode S π depth marks M (ident i)

end
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end OAI
