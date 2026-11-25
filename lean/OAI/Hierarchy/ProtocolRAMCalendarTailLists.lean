import OAI.Hierarchy.ProtocolRAMCalendarMesh

namespace OAI
/-! # Explicit public event lists between replay attempts -/
namespace Hierarchy.ProtocolRAM.Calendar

def trialTail (c : Mesh) (p h extra : ℕ) : List Event :=
  (List.range c.reserveSteps).flatMap (reserveBlock c p h) ++
    ((List.range extra).map ((h+1)+·)).flatMap (trialBlock c p)

def phaseTail (c : Mesh) (p h extra b : ℕ) : List Event :=
  trialTail c p h (c.outerFuel-(h+1)) ++ [.feed (.outer p)] ++
    ((List.range extra).map ((p+1)+·)).flatMap (outerBlock c) ++
    (List.range b).flatMap (trialBlock c (p+1+extra))

def innerTail (p h j b extra : ℕ) : List Event :=
  ((List.range extra).map ((b+1)+·)).map (fun i => .attempt (.inner p h j i))

def reserveTail (c : Mesh) (p h j b extra trial : ℕ) : List Event :=
  innerTail p h j b (c.innerFuel-(b+1)) ++ [.feed (.inner p h j)] ++
    ((List.range extra).map ((j+1)+·)).flatMap (reserveBlock c p h) ++
    (List.range trial).map (fun i => .attempt (.inner p h (j+1+extra) i))

def purchaseTail (c : Mesh) (p h j b : ℕ) : List Event :=
  (List.range j).flatMap (reserveBlock c p h) ++
    (List.range b).map (fun i => .attempt (.inner p h j i))

end Hierarchy.ProtocolRAM.Calendar

end OAI
