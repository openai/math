import OAI.Computability.BorderVNP.DiagonalPublishedOwnerWidth

/-! # Native source placement retained together with the issued cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM CellPacket CellPacketGeometry.History.Native CellDispatch CompactMachine CellSparse

variable {Key Slot : Type} {C n : ℕ}

/-- The marker-indexed geometric directory which generated a sparse source.
The retained physical field includes the restored exterior and all signed
report bits on the same cell. -/
abbrev SavedSparsePlacement (directory : CellPacketGeometry.SiteWords.Directory Key Slot (C+1))
    (logical : ℕ → CellInput) : Type :=
  PLift (∃ (places : Fin (C+1) → Placed Slot) (extras : ℕ → List Record) (fields : ℕ → SparseExterior.Field),
    TypedBatch.SourceShape places directory ∧
    logical=fun i => SparseExterior.logicalCell (Terminal.placeAt places i) (extras i) (fields i))

/-- Preserve the recorded destination ordinals and exact source received from
the sparse call generator in one copy of the geometric report data. -/
def savedSparsePlacement (directory : CellPacketGeometry.SiteWords.Directory Key Slot (C+1))
    (places : Fin (C+1) → Placed Slot) (shape : TypedBatch.SourceShape places directory)
    (patch : ℕ → Placed Slot) (placed : patch=Terminal.placeAt places) (extras : ℕ → List Record)
    (fields : ℕ → SparseExterior.Field) (logical : ℕ → CellInput)
    (generated : logical=fun i => SparseExterior.logicalCell (patch i) (extras i) (fields i)) :
    SavedSparsePlacement directory logical :=
  ⟨⟨places,extras,fields,shape,placed ▸ generated⟩⟩

namespace PinStart

open BorderVNP.Cube
variable {T dim box lanes candidates symbols w : ℕ} {X Y : Type}
    {KeyAt SlotAt : Y → Type} {cellsAt : Y → ℕ}

/-- The physical marker and sparse field record for one original team. -/
def savedPlacementAt (directory : (f : Y) → CellPacketGeometry.SiteWords.Directory
    (KeyAt f) (SlotAt f) (cellsAt f+1))
    (id : TableEntry dim box lanes candidates symbols → ℕ) (U : X → Fin (T+1) → PinStart SparseExterior.driver n w)
    (f : Y) (z : Σ x, JointPrefix id (U x)) (u : Fin (T+1)) (native : SparseSource id (U z.1) (z.2 u)) : Type :=
  SavedSparsePlacement (directory f) native.logicalAt

/-- The saved placement for each team depends on the selected original
history and on the exact sparse source from that native return. -/
def savedPlacements (directory : (f : Y) → CellPacketGeometry.SiteWords.Directory
    (KeyAt f) (SlotAt f) (cellsAt f+1))
    (id : TableEntry dim box lanes candidates symbols → ℕ) (U : X → Fin (T+1) → PinStart SparseExterior.driver n w)
    (f : Y) (z : Σ x, JointPrefix id (U x)) (native : (u : Fin (T+1)) → SparseSource id (U z.1) (z.2 u)) : Type :=
  (u : Fin (T+1)) → savedPlacementAt directory id U f z u (native u)

end PinStart

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
