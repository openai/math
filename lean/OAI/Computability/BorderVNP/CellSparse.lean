import Mathlib.Data.List.Basic

/-!
# Sparse records for the private cell contraction (§§7.3, 8.3 and 11)

Addresses count bits in the cell's assignment bank. Internal wires occupy one slot each
and supplied boundary and delivery bits follow them. A one-copy site box lives in a
directory and can be invoked at many strides without duplicating its description.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- A rectangular bit slice. Copies advance by `copyStride`, lanes by `laneStride`. -/
structure Port where
  /-- Starting assignment-bank position. -/
  base : ℕ
  /-- Distance between corresponding bits of consecutive copies. -/
  copyStride : ℕ
  /-- Distance between consecutive lanes in a copy. -/
  laneStride : ℕ
  deriving DecidableEq

/-- Number of a single bit in a repeated port. -/
def Port.atBit (p : Port) (copy lane : ℕ) : ℕ := p.base + copy * p.copyStride + lane * p.laneStride

/-- A one-copy private factor. A row is addressed in little-endian order by the
listed relative wire indices. A Boolean table passes or rejects the assignment.
A signed table toggles its sign on true rows. A gadget table counts its selected
position even if that position will later evaluate to the field scalar zero. -/
inductive Factor where
  | truth (wires : List ℕ) (rows : List Bool)
  | sign (wires : List ℕ) (negativeRows : List Bool)
  | gadget (wires : List ℕ) (position : List ℕ)
  | unary (wire : ℕ) (reportedUse : Port)
  deriving DecidableEq

/-- Route one term's original input lanes to the compact cable indexed by the
number of strictly earlier occurrences of that term in the selector word. -/
structure Route where
  /-- Term code whose copies use this route. -/
  term : ℕ
  /-- Number of lanes in each occurrence. -/
  lanes : ℕ
  /-- Port addressed by original copy index. -/
  original : Port
  /-- Port addressed by occurrence index within the term. -/
  compact : Port
  deriving DecidableEq

/-- Public descriptors for repeated local constraints. Concatenation is equality
on consecutive ranges. For a box, `id` selects private metadata stored once. -/
inductive Record where
  | zero (copies lanes : ℕ) (p : Port)
  | equal (copies lanes : ℕ) (src dst : Port)
  | box (id base copies stride : ℕ)
  | profile (copies : ℕ) (selector : Port) (selectorWidth : ℕ)
      (histogram : List ℕ) (routes : List Route)
  deriving DecidableEq

/-- A cell input provides a private box directory and the sparse public rows.
Multiplicity bits report the number of selected positions with a given gadget ID. -/
structure Directory where
  /-- Per-site private one-copy factor descriptions. -/
  boxes : List (List Factor)
  /-- Public wiring and profile descriptions. -/
  records : List Record
  /-- Little-endian bit addresses of the proposed count for each gadget ID. -/
  reportedCounts : List (List ℕ)
  deriving DecidableEq

/-- Read a little-endian nonnegative integer at an ordered list of bit addresses. -/
def word (bank : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | a :: xs => (if bank a then 1 else 0) + 2 * word bank xs

/-- The bit addresses occupied by one copy of a contiguous or strided port. -/
def Port.lanes (p : Port) (copy width : ℕ) : List ℕ :=
  (List.range width).map (p.atBit copy)

/-- A profile's selected term at a copy. -/
def label (bank : ℕ → Bool) (selector : Port) (width i : ℕ) : ℕ :=
  word bank (selector.lanes i width)

/-- Number of occurrences strictly before the named copy. -/
def earlier (bank : ℕ → Bool) (selector : Port) (width term i : ℕ) : ℕ :=
  ((List.range i).map (label bank selector width)).count term

/-- All selector codes are in range, the advertised histogram is correct, and
the lanes of each selected term are in occurrence order on its compact cable. -/
def profileValid (bank : ℕ → Bool) (copies : ℕ) (selector : Port) (width : ℕ)
    (histogram : List ℕ) (routes : List Route) : Prop :=
  (∀ i < copies, label bank selector width i < histogram.length) ∧
  (∀ a : Fin histogram.length, earlier bank selector width a copies = histogram[a]) ∧
  ∀ r ∈ routes, r.term < histogram.length ∧ ∀ i < copies, label bank selector width i = r.term →
    ∀ lane < r.lanes, bank (r.original.atBit i lane) =
      bank (r.compact.atBit (earlier bank selector width r.term i) lane)

end CellSparse

end BorderVNP
end Computability
end OAI
