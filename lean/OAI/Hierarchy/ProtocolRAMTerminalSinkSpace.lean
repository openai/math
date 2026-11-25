import OAI.Hierarchy.ProtocolRAMSinkData
import OAI.Hierarchy.ProtocolRAMCoreRouteOrder
import OAI.Hierarchy.ProtocolRAMCatalogueRowFields

namespace OAI
/-! # Physical catalogue sink and its seven native output words -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
namespace CatalogueRows

/-- The same native geometry program supplies the early posted link prices and the
endpoints published by the terminal reporter. -/
def Board.sink (b : Board) (r : ℕ) (banks : RouteSettlement.Banks)
    (source table destination : ℕ) (owners : Bank) : Sink r b.rows :=
  ⟨banks,source,table,destination,owners,b.geometry⟩

end CatalogueRows
namespace CoreRoute
variable {z W k edges : ℕ}
local notation "r" => Fintype.card (Slots z (2^W) k)

/-- Scalar conditions for the three word banks and the native reporter. -/
structure SinkSpace (s : Sink r edges) (w : ℕ) : Prop where
  kind : s.banks.kind.base+s.banks.kind.size≤ s.banks.reserved.base
  index : s.banks.index.base+s.banks.index.size≤ s.banks.reserved.base
  ownerReserve : s.owners.base+s.owners.size≤ s.banks.reserved.base
  ownerWidth : s.owners.base+s.owners.size≤ s.banks.width.base
  inputs : (RouteSettlement.words s.banks).Fits w s.source
  source : s.source+2*r<2^w
  width : s.banks.width.base+edges≤ s.source
  wide : 3<w
  fields : (ProtocolRAM.packed s.owners (RouteSettlement.fields s.banks s.geometry)).Fits w s.table
  table : s.table+8*edges<2^w
  destination : s.destination+9*edges<2^w
  apart : s.table+8*edges≤ s.destination ∨ s.destination+9*edges≤ s.table

end CoreRoute
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
