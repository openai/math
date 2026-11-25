import OAI.Computability.BorderVNP.PackedBundleCopy
import OAI.Computability.BorderVNP.PackedBottomBundleHeader

/-! # Compacting the live sorted six-word bundle directory

The stable geometry sort returns a payload array and an inverse-rank array.
Two ranks give the exact sorted interval for every global cell. This fixed
assembly fragment copies just those intervals, writes the first and past
bundle ordinals, and advances through empty cells as well.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BundleDirectory

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA

/-- Global frame and the four distinct directory allocations. -/
structure Layout where
  /-- Global ABI frame base. -/
  frame : ℕ
  /-- Address in global frame slot 92 of the 22-word tally-control table. -/
  control : ℕ
  /-- Number of final cells, in frame slot 15. -/
  cells : ℕ
  /-- Number of original retained bundles, in frame slot 66. -/
  bundles : ℕ
  /-- First/past ordinal output array in control word 18. -/
  ranges : ℕ
  /-- Compacted six-word rows in control word 19. -/
  output : ℕ
  /-- Sorted payload bank in control word 20. -/
  payload : ℕ
  /-- Inverse-rank bank in control word 21. -/
  rank : ℕ

/-- The stop markers occur after the start markers and all six-word input rows. -/
def Layout.stopRank (l : Layout) := l.rank+l.cells+6*l.bundles

/-- Absolute addresses of the first and one-past-last actual source words of a cell. -/
def Layout.start (l : Layout) (m : ℕ → ℕ) (c : ℕ) := l.payload+m (l.rank+c)+1

/-- Absolute address of the right marker. -/
def Layout.stop (l : Layout) (m : ℕ → ℕ) (c : ℕ) := l.payload+m (l.stopRank+c)

/-- Read one fixed field of the tally-control directory. -/
private def controlField (dst : Reg) (k : Word 8) : Code :=
  .block [.constant 63 k,.binary .add 62 60 63,.load dst 62]

/-- Load C, N, both input banks, both output banks, and the scalar constants. -/
def setup : Code := .block [readFrame 31 62 63 15,readFrame 34 62 63 66,
  readFrame 60 62 63 92,controlField 35 18,controlField 36 19,
  controlField 32 20,controlField 33 21,.constant 37 6,.binary .mul 34 37 34,
  .binary .add 34 31 34,.binary .add 34 33 34,.copy 52 36,.constant 38 0,.constant 39 0,
  .constant 63 1]

/-- Read the two ranks and skip the left marker to obtain a half-open copy range. -/
def openSection : Code := .block [.binary .add 40 33 38,.load 40 40,
  .binary .add 41 34 38,.load 41 41,.binary .add 50 32 40,.binary .add 50 50 63,
  .binary .add 51 32 41]

/-- Write bundle ordinals (one per six scalar words), then advance to the next cell. -/
def closeSection : Code := .block [.store 35 39,.binary .add 35 35 63,
  .binary .sub 39 52 36,.binary .div 39 39 37,.store 35 39,
  .binary .add 35 35 63,.binary .add 38 38 63]

/-- Both pointer words are written even if the selected range is empty. -/
def cellStep : Code := .block [openSection,copySection,closeSection]

/-- Length-independent native compaction after the marked sort's physical return. -/
def program : Code := .seq setup (.whileLt 38 31 cellStep)

/-- Header values read from the actual shared frame. -/
def Layout.loaded (l : Layout) (frameBase : ℕ) (m : ℕ → ℕ) : Prop :=
  frameBase = l.frame ∧ m (l.frame+15) = l.cells ∧ m (l.frame+66) = l.bundles ∧
  m (l.frame+92) = l.control ∧ m (l.control+18) = l.ranges ∧ m (l.control+19) = l.output ∧
  m (l.control+20) = l.payload ∧ m (l.control+21) = l.rank

/-- Half-open disjoint allocations; either physical address order is allowed. -/
def apart (a len b size : ℕ) : Prop := a+len ≤ b ∨ b+size ≤ a

/-- End pointers and all addresses used by the native fragment fit the hardware word width. -/
structure Layout.Fits (l : Layout) (w width : ℕ) : Prop where
  /-- The last scalar in the global frame header can be addressed. -/
  frameEnd : l.frame+92 < 2^w
  /-- The last control word can be addressed. -/
  controlEnd : l.control+21 < 2^w
  /-- Capacity of each of the two stable sort banks. -/
  markers : l.cells+6*l.bundles+l.cells ≤ width
  /-- The one-past pointer of the sorted payload bank fits. -/
  payloadEnd : l.payload+width < 2^w
  /-- The one-past pointer of the inverse-rank bank fits. -/
  rankEnd : l.rank+width < 2^w
  /-- The two-word cell range pointer fits, including at termination. -/
  rangesEnd : l.ranges+2*l.cells < 2^w
  /-- The six-word bundle pointer fits, including at termination. -/
  outputEnd : l.output+6*l.bundles < 2^w
  /-- Range words and bundle fields occupy separate banks. -/
  rangesOutput : apart l.ranges (2*l.cells) l.output (6*l.bundles)
  /-- Range writes preserve all live rank words. -/
  rangesRank : apart l.ranges (2*l.cells) l.rank width
  /-- Range writes preserve the sorted source words. -/
  rangesPayload : apart l.ranges (2*l.cells) l.payload width
  /-- Bundle writes preserve the inverse-rank bank. -/
  outputRank : apart l.output (6*l.bundles) l.rank width
  /-- Bundle writes preserve the sorted payload bank. -/
  outputPayload : apart l.output (6*l.bundles) l.payload width

end Packing.BundleDirectory

end BorderVNP
end Computability
end OAI
