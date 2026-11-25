import OAI.Computability.BorderVNP.CellPacketGeometryOriginalRoster

/-! # Inputs for the original private-box directory of a packed history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open Packing.Inherited FrozenTape SiteWords

/-- The two retained tape schemas and the input rows from which the packet
builder computes the directory of the original private boxes. -/
structure OriginalGeometry (entries cells : ℕ) where
  /-- Number of original site rows, including public site rows. -/
  nr : ℕ
  /-- Common upper bound on tags per tape row. -/
  cap : ℕ
  /-- Number of pin bits for each first-tape input. -/
  oldWidth : ℕ
  /-- Number of pin bits for each final binding input. -/
  tieWidth : ℕ
  /-- Type of row indices in the first tape schema. -/
  OldAT : Type
  /-- Type of input indices in the first tape schema. -/
  OldBT : Type
  /-- Type of row indices in the final binding schema. -/
  TieAT : Type
  /-- Type of input indices in the final binding schema. -/
  TieBT : Type
  /-- Arguments used by the cell-size and report columns. -/
  Scope : Type
  /-- Schema of the retained history rows. -/
  oldSchema : FrozenTape.Schema OldAT OldBT
  /-- Schema of the final binding rows. -/
  tieSchema : FrozenTape.Schema TieAT TieBT
  /-- Original site row occupied by each private transmission entry. -/
  inputEntry : Fin entries ↪ Fin nr
  /-- Public factor tables stored at the other original site rows. -/
  known : Fin nr → List (List CellSparse.Factor)
  /-- Every retained history row fits the common tag bound. -/
  oldCap : ∀ j, (oldSchema.tags j).length ≤ cap
  /-- Every final binding row fits the common tag bound. -/
  tieCap : ∀ j, (tieSchema.tags j).length ≤ cap
  /-- Source argument for the private-wire count at each cell. -/
  privateArgs : Fin (cells + 1) → Scope
  /-- Source arguments for the report digits at each cell. -/
  reportArgs : Fin (cells + 1) → List (List Scope)
  /-- Numeric value of a source argument. -/
  geometryArg : Scope → ℕ
  /-- Input assignment for the retained history rows. -/
  oldPins : Pins OldAT OldBT oldWidth → Bool
  /-- Input assignment for the final binding rows. -/
  tiePins : Pins TieAT TieBT tieWidth → Bool
  /-- Receiving cell of each original site row. -/
  originCell : Fin nr → Fin cells
  /-- Wire displacement for shifting the retained rows at each site. -/
  oldOff : Fin nr → ℕ
  /-- Box displacement for rebasing the retained rows at each site. -/
  oldBox : Fin nr → ℕ

/-- Build the packet directory, using the original transmission embedding to
distinguish a private box from a public table on each input row. -/
noncomputable def OriginalGeometry.directory {entries cells : ℕ} (g : OriginalGeometry entries cells) :
    SiteWords.Directory (Fin (roster g.nr g.oldSchema g.tieSchema).length) (Fin entries) (cells + 1) :=
  History.directory g.oldSchema g.tieSchema (originalBoxes g.inputEntry g.known) g.oldCap g.tieCap
    g.privateArgs g.reportArgs g.geometryArg g.oldPins g.tiePins g.originCell g.oldOff g.oldBox

end CellPacketGeometry.History

end BorderVNP
end Computability
end OAI
