import OAI.Computability.BorderVNP.CubePhysicalReportReaders

/-! # The operand readers on the native report tape for a single path -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.ReceivedRows

open Crossing Diagonal.CellEntries DiagonalTallyCellReports NativeLedger
open scoped Classical

/-- The report tape supplies the operands in the physical cell order and native
vertex order of the given path, at the actual cursors for every team. -/
noncomputable def pathReportReaders {D C n d blocks b h K s T B : ℕ} {P : Type} {bits : P → ℕ}
    {N : Network D P bits} {cell : N.Site → Fin C} {l : ReportLayout}
    (R : ReceivedRows (fun _ : Fin T => l) C)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b))
    (tags : N.Tables (Entry (Fin l.parameters) (Fin l.gadgets))) (x : Ports bits)
    (words : PowerWords (Fin T) (Fin l.parameters) (Fin l.gadgets) B N tags)
    (label : Fin C → Label (n+1) d) (team : Fin d → Fin T) (a : Path N cell n d blocks b h K s)
    (hosted : ∀ j,pathCellOwner label team a (R.order j)=j.1)
    (tape : Fin T → ℕ → Bool) (start : Fin T → ℕ) (t : Fin T) : Type :=
  let o := R.ledgerOrder (N:=N) (cell:=cell) (H:=l.parameters) (U:=l.gadgets) (B:=B) tags words label team a hosted t
  ReportReaders (N:=N) (cell:=cell) (l:=l) (B:=B) slot tags x words label team a t
    (Orders.withNativeVertices (N:=N) (cell:=cell) (B:=B) tags words label team a t o) (R.reportedWithTape tape start)

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
