import OAI.Computability.BorderVNP.RoutingISACubeArenaFields

/-! # Address reservations for sparse external-input transport

The emitted quad rows comprise both ends of each geometric cable plus the
genuine surviving free-data intervals. The native bucket groups them by
receiving cell and preserves their order. The length-only compact output
windows may be larger than the streams actually written.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentArena

/-- Scalar input sizes, all fixed before decoding a geometry history. -/
structure Layout where
  /-- First free address after the immutable cube tables. -/
  start : ℕ
  /-- Number of geometric cable slots. -/
  cables : ℕ
  /-- Upper bound on raw literal delivery rows. -/
  deliveries : ℕ
  /-- Number of possible receiving cells. -/
  cells : ℕ
  /-- Address stride between two compressed external streams. -/
  stride : ℕ

/-- Capacity for both cable ends, all literal delivery spans and a terminal word. -/
def Layout.capacity (l : Layout) := 2*l.cables+l.deliveries+1

/-- Absolute address of each physical region, in allocation order. -/
def Layout.quads (l : Layout) := l.start

/-- Two grouping prefix words per cell, after the four-word emitted descriptors. -/
def Layout.pairs (l : Layout) := l.quads+4*l.capacity

/-- Compacted logical-start, actual-source and width triples. -/
def Layout.triples (l : Layout) := l.pairs+2*l.cells

/-- Grouped insertion cursors for the stable bucket pass. -/
def Layout.cursors (l : Layout) := l.triples+3*l.capacity

/-- One variable-length compressed output at each fixed-stride start. -/
def Layout.external (l : Layout) := l.cursors+l.cells

/-- Actual compressed bit count for each owned cell. -/
def Layout.counts (l : Layout) := l.external+l.cells*l.stride

/-- First subsequent memory reservation. -/
def Layout.limit (l : Layout) := l.counts+l.cells+1

/-- Actual scalar words reconstructed at frame-92 controls 28 through 36.
The emitter replaces the initial capacity by the populated row count. -/
def Layout.controls (l : Layout) (old : ℕ → ℕ) : ℕ → ℕ
  | 28 => l.quads | 29 => l.capacity | 30 => l.cells | 31 => l.pairs | 32 => l.triples
  | 33 => l.cursors | 34 => l.external | 35 => l.stride | 36 => l.counts | i => old i

/-- The complete numerical memory span. -/
theorem Layout.footprint (l : Layout) : l.limit = l.start+7*l.capacity+4*l.cells+l.cells*l.stride+1 := by
  simp only [limit,counts,external,cursors,triples,pairs,quads]
  ring

/-- The address allocation, including all unfilled per-cell windows, is
polynomial in the length-only scalar maxima. -/
theorem Layout.polynomial_room (l : Layout) {q : ℕ} (m : l.cables ≤ q) (d : l.deliveries ≤ q)
    (c : l.cells ≤ q) (s : l.stride ≤ q) : l.limit ≤ l.start+32*(q+1)^2 := by
  rw [l.footprint,capacity]
  have prod := Nat.mul_le_mul c s
  nlinarith

end RoutingISA.FragmentArena

end BorderVNP
end Computability
end OAI
