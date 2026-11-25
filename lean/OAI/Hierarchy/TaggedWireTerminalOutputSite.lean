import OAI.Hierarchy.TaggedWireTerminalOriginal
import OAI.Hierarchy.TaggedWireTerminalPorts

namespace OAI
/-! # Geometric endpoints of every native output word of positive width -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment
open AdaptiveProbe ProbeStage CoreBoard ReportSockets WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical
variable {h W k attempts M : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marked : Marks h W k attempts) (unique : Exclusive marked)
    (b : Board) (order : Fin b.coreRows≃Edges S h (2^W) k) (acquired : Bought S π depth marked→Fin b.boughtRows)
    (raw : Fin b.rows→ProtocolRAMEmit.Row)
local notation "ordinal" => b.original S π depth marked order acquired
local notation "name" => siteNumber h (2^W) k
local notation "K" => siteLast h (2^W) k+1
variable (receipt : Alignment b S π depth marked M raw (fun i=>(raw i).width)
    (b.original S π depth marked order acquired))
variable (B : Mount (S:=S) π (siteNumber h (2^W) k) b.rows) (pad : Chord (siteLast h (2^W) k+1))

/-- Materializing an edge from its two native fields gives exactly the sorted
original edge, even if its entire output width is consumed by other routes. -/
theorem edgeOfWord (i : Active b raw)
    (tail : (B.actual.tail i.val).val=(raw i.val).endpoint)
    (head : (B.actual.head i.val).val=(raw i.val).opposite) :
    filledChord B.actual pad i.val=HistoryRoles.sorted S π depth marked (.inl (receipt.ident i)) := by
  let z:=actualEnds S π depth marked (receipt.ident i)
  have distinct : name z.1≠name z.2:=(name).injective.ne (actual_distinct S π depth marked (receipt.ident i))
  change filledChord B.actual pad i.val=orderedChord (name z.1) (name z.2) distinct
  rcases receipt.joins i with fwd|rev
  · have one:B.actual.tail i.val=name z.1:=Fin.ext (tail.trans fwd.1)
    have two:B.actual.head i.val=name z.2:=Fin.ext (head.trans fwd.2)
    simp [filledChord,one,two,distinct]
  · have one:B.actual.tail i.val=name z.2:=Fin.ext (tail.trans rev.1)
    have two:B.actual.head i.val=name z.1:=Fin.ext (head.trans rev.2)
    by_cases lt:name z.1<name z.2
    · simp [filledChord,one,two,distinct.symm,orderedChord,lt,not_lt.mpr lt.le]
    · have gt:name z.2<name z.1:=lt_of_le_of_ne (le_of_not_gt lt) distinct.symm
      simp [filledChord,one,two,distinct.symm,orderedChord,lt,gt]

theorem original_site (i : Active b raw) (s : Bool)
    (tail : (B.actual.tail i.val).val=(raw i.val).endpoint)
    (head : (B.actual.head i.val).val=(raw i.val).opposite) :
    name (HistoryRoles.site S (originalPort S π depth marked unique b order acquired raw receipt i s))=
      (portGraph K).vertex (filledChord B.actual pad i.val) s := by
  rw [edgeOfWord S π depth marked b order acquired raw receipt B pad i tail head]
  let order0:Fin (Fintype.card (HistoryRoles.Source S π depth marked))≃HistoryRoles.Source S π depth marked:=
    (Fintype.equivFin _).symm
  have placed:=HistoryRoles.named_site S π depth marked unique order0 (order0.symm (.inl (receipt.ident i))) s
  simpa [originalPort,sourceSide,HistoryRoles.named,HistoryRoles.orient,order0,HistoryRoles.physical] using placed

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment

end
end OAI
