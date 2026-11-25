import OAI.Computability.BorderVNP.CellPacketGeometryOriginalInputs
import OAI.Computability.BorderVNP.PackedFrozenOriginalCellOwner

/-! # Cell ownership in the directory of original inputs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

/-- An original site description appears exactly in the cell named by its
embedded source row. This statement also covers cells with no private box. -/
theorem OriginalGeometry.original_receiver {entries cells : ℕ} (g : OriginalGeometry entries cells)
    (c : Fin cells) (j : Fin entries) :
    Sum.inr j ∈ g.directory.cellBoxes c.castSucc ↔ g.originCell (g.inputEntry j)=c :=
  directory_original_owner g.oldSchema g.tieSchema (originalBoxes g.inputEntry g.known) g.oldCap g.tieCap
    g.privateArgs g.reportArgs g.geometryArg g.oldPins g.tiePins g.originCell g.oldOff g.oldBox
    g.inputEntry g.known rfl c j

end CellPacketGeometry.History

end BorderVNP
end Computability
end OAI
