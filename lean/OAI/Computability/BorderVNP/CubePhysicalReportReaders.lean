import OAI.Computability.BorderVNP.CubePhysicalReceivedLedgerOrder

/-! # The native count and use readers that identify a physical path subtotal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open Crossing Diagonal.CellEntries DiagonalTallyCellReports DiagonalTallyMaterialize
open scoped Classical

variable {D C n d blocks b h K s T B : ℕ} {P : Type} {bits : P → ℕ}
    {N : Network D P bits} {cell : N.Site → Fin C} {l : ReportLayout}
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b))
    (tags : N.Tables (Entry (Fin l.parameters) (Fin l.gadgets))) (x : Ports bits)
    (words : PowerWords (Fin T) (Fin l.parameters) (Fin l.gadgets) B N tags)
    (label : Fin C → Label (n+1) d) (team : Fin d → Fin T) (a : Path N cell n d blocks b h K s)
    (t : Fin T) (o : Orders tags words label team a t) (reports : Fin C → ReportCell l)
local notation3 (prettyPrint := false) "cs" => teamReports tags words label team a t o reports

/-- The actual passing sparse call of each cell supplies its complete checked
scalar rows in the native numbering and its observed report addresses. -/
structure ReportCellReaders (reports : Fin C → ReportCell l) where
  /-- The ordered count reader at each physically assigned cell. -/
  cells : ∀ c, CellRead {v : N.Site // cell v=c} l.gadgets
  siteID : ∀ c (v : {v : N.Site // cell v=c}) g, (((cells c).observed v).filterMap Prod.snd).count g.val =
    (counters (tags v.val (pathEdges slot a v.val) (fun p => x p.val))).2 g
  fields : ∀ c,(cells c).directory.reportedCounts=countFields ((reports c).privateWires+(reports c).supplied)
    l.gadgets l.countWidth
  digits : ∀ c g j,(reports c).counts g j=(cells c).bank
    ((reports c).privateWires+(reports c).supplied+g.val*l.countWidth+j.val)

/-- All operands read from a real signed report table: physical selected-bit
addresses, per-cell scalar counts, and the chronological ownership bijection. -/
structure ReportReaders where
  /-- Pointers of the native unary occurrence at its owning report cursor. -/
  use : PowerSlot (Fin T) (Fin l.parameters) B → UseRead
  /-- The ordered count reader at each physically assigned cell. -/
  cells : ∀ c, CellRead {v : N.Site // cell v=c} l.gadgets
  /-- Native report occurrences in bijection with this team's original numbered powers. -/
  source : UseOccurrence cs ≃ {i // routedPowerOwner tags words label team a i=t}
  useBit : ∀ i, (use i).bit=words.localUse (pathEdges slot a) (fun _ p => x p.val) i.1 i.2.1 i.2.2
  align : ∀ row, let i := (source row).val
    occurrencePair cs row=(i.2.1.val,if (use i).bit then 2^i.2.2.val else 0)
  siteID : ∀ c (v : {v : N.Site // cell v=c}) g,(((cells c).observed v).filterMap Prod.snd).count g.val =
    (counters (tags v.val (pathEdges slot a v.val) (fun p => x p.val))).2 g
  fields : ∀ c,(cells c).directory.reportedCounts=countFields ((reports c).privateWires+(reports c).supplied)
    l.gadgets l.countWidth
  digits : ∀ c g j,(reports c).counts g j=(cells c).bank
    ((reports c).privateWires+(reports c).supplied+g.val*l.countWidth+j.val)

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI
