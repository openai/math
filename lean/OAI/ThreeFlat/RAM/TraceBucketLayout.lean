import OAI.ThreeFlat.Diagonal.TraceSourceDigits

namespace OAI
/-! # Public dimensions and native row addresses of the first history atom -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Diagonal.TraceSourceOwner

/-- The current trace dimensions, addresses of its stored records and
small public lookup tables, and field-dependent scalar library labels. -/
structure Layout where
  shape : Shape
  low : ℕ
  depth : ℕ
  slots : ℕ
  copies : ℕ
  records : ℕ
  dictionary : ℕ
  masks : ℕ
  tableIds : ℕ
  equalId : ℕ
  zeroId : ℕ
  unitId : ℕ

def Layout.lowRows (s : Layout) := 2^s.low
def Layout.gates (s : Layout) := s.lowRows*s.slots
def Layout.per (s : Layout) := s.lowRows*(s.slots*3)
def Layout.tags (s : Layout) := (1+(s.depth+s.depth))*s.per
def Layout.arcs (s : Layout) := (s.copies+1)*2
def Layout.bank (s : Layout) := s.arcs*s.tags
def Layout.relays (s : Layout) := s.bank+s.tags

def Layout.pinLow (s : Layout) (lane : ℕ) := lane*s.lowRows*2
def Layout.pinCount (s : Layout) (lane : ℕ) := min (s.shape.header-s.pinLow lane) (2*s.lowRows)
def Layout.readAt (s : Layout) (site slot leg : ℕ) := s.records+11*(site*s.slots+slot)+leg

end ThreeFlat.RAM.TraceBucketAtom

end OAI
