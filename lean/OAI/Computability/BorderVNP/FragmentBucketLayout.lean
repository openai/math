import OAI.Computability.BorderVNP.RoutingISATableState
import OAI.Computability.BorderVNP.TransmissionCost

/-! # Physical arrays of the per-cell sparse input interval directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FragmentBucket

open RoutingISA

/-- Bases of the source quadruples, two-word cell headers, output triples and
one writable cursor per cell. All counts are in words or records as indicated. -/
structure Layout where
  /-- Base address of the four-word input records, each carrying a cell index and three payload words. -/
  quads : ℕ
  /-- Number of input records to distribute among the cells. -/
  rows : ℕ
  /-- Number of cell buckets in the directory. -/
  cells : ℕ
  /-- Base address of the two-word headers holding each cell’s start and record count. -/
  pairs : ℕ
  /-- Base address of the three-word payload records after stable grouping by cell. -/
  triples : ℕ
  /-- Base address of the writable cursor for each cell during the distribution pass. -/
  cursors : ℕ

/-- Half-open disjoint address ranges, allowing either physical order. -/
def apart (a width b size : ℕ) : Prop := a+width ≤ b ∨ b+size ≤ a

/-- Exact allocated extents, including the zero-row and zero-cell cases. -/
structure Layout.Fits (l : Layout) (w : ℕ) : Prop where
  literals : 4 < 2^w
  rowCount : l.rows < 2^w
  cellCount : l.cells < 2^w
  quadEnd : l.quads+4*l.rows ≤ 2^w
  pairEnd : l.pairs+2*l.cells ≤ 2^w
  tripleEnd : l.triples+3*l.rows ≤ 2^w
  cursorEnd : l.cursors+l.cells ≤ 2^w
  qp : apart l.quads (4*l.rows) l.pairs (2*l.cells)
  qt : apart l.quads (4*l.rows) l.triples (3*l.rows)
  qc : apart l.quads (4*l.rows) l.cursors l.cells
  pt : apart l.pairs (2*l.cells) l.triples (3*l.rows)
  pc : apart l.pairs (2*l.cells) l.cursors l.cells
  tc : apart l.triples (3*l.rows) l.cursors l.cells

/-- Six persistent register values for all three stable counting-sort passes. -/
def Layout.Ready (l : Layout) (z : NatState) : Prop :=
  z.reg 2 = l.quads ∧ z.reg 3 = l.rows ∧ z.reg 4 = l.cells ∧
    z.reg 5 = l.pairs ∧ z.reg 6 = l.triples ∧ z.reg 7 = l.cursors

/-- The input emission has produced these sparse positive intervals, in public
occurrence order. Positivity of their lengths is checked by the producer. -/
structure Layout.Input (l : Layout) (tag : Fin l.rows → Fin l.cells)
    (payload : Fin l.rows → Fin 3 → ℕ) (mem : ℕ → ℕ) : Prop where
  cell : ∀ i, mem (l.quads+4*i.val) = (tag i).val
  field : ∀ i j, mem (l.quads+4*i.val+1+j.val) = payload i j

/-- Writes within disjoint half-open arrays cannot alter the same address. -/
theorem apart_ne {a b w v i j : ℕ} (h : apart a w b v) (hi : i < w) (hj : j < v) : a+i ≠ b+j := by
  rcases h with h|h <;> omega

end FragmentBucket

end BorderVNP
end Computability
end OAI
