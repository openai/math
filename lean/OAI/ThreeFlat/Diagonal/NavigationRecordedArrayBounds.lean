import OAI.ThreeFlat.Diagonal.PhysicalStateWidth
import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily
import OAI.ThreeFlat.Diagonal.NavigationDirectory

namespace OAI
/-! # Address ranges for the predecessor arrays of an issued native stage -/

namespace ThreeFlat.Diagonal.NavigationPass
open PhysicalStage NavigationDirectory

/-- Complete address ranges of the old numbered slot graph and the old width table. -/
structure OldArrayBounds (low : ℕ) (c : Cursor) {d l : ℕ} (X : State d l) : Prop where
  graphLow : low≤c.graph
  widthLow : low≤c.width
  graphBound : c.graph+6*(Fintype.card X.Base*d)≤c.heap
  widthBound : c.width+X.edgeCount≤c.heap

theorem OldArrayBounds.lower {lo hi d l : ℕ} {c : Cursor} {X : State d l}
    (room : OldArrayBounds hi c X) (bound : lo≤hi) : OldArrayBounds lo c X :=
  ⟨bound.trans room.graphLow,bound.trans room.widthLow,room.graphBound,room.widthBound⟩

/-- The address and width bounds of the issued occurrence at its original cursor. -/
structure RecordedArrayBounds (W head : ℕ) (c : Cursor) {d l : ℕ} (X : State d l)
    : Prop extends OldArrayBounds head c X where
  headerLow : 21*(2^(W/16))^4 ≤ c.header
  denseLow : head ≤ c.dense
  headerDense : c.header+64≤c.dense
  widthPos : 0 < c.width
  wire : X.maxWidth+1 ≤ (2^(W/16))^4

instance {W head d l : ℕ} {c : Cursor} {X : State d l} :
    CoeOut (RecordedArrayBounds W head c X) (OldArrayBounds head c X) :=
  ⟨RecordedArrayBounds.toOldArrayBounds⟩

end ThreeFlat.Diagonal.NavigationPass

end OAI
