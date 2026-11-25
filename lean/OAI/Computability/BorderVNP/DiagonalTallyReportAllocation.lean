import OAI.Computability.BorderVNP.DiagonalTallyReportBatchCost

/-! # Length-only address reservations for the native report and selected-cube stages -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyAllocation

/-- Length-only ceilings for the two private scratch partitions of a processor. -/
structure Bounds where
  /-- Total number of global cells, bounding the owned subset as well. -/
  cells : ℕ
  /-- Total number of retained one-copy site descriptions. -/
  bundles : ℕ
  /-- Upper bound on marked one-copy positions in a single retained description. -/
  marked : ℕ
  /-- Bound on the expanded marked copies among all cells of the processor. -/
  uses : ℕ
  /-- Fixed gadget coordinate count. -/
  gadgets : ℕ
  /-- Width of each cell gadget count. -/
  countWidth : ℕ
  /-- Bound on actual owned cube vertices. -/
  vertices : ℕ
  /-- Fixed number of bit references for a cube lookup. -/
  cubeWidth : ℕ
  /-- Upper bound on supplemental checker words in any one cell. -/
  supplementStride : ℕ

/-- The per-cell controls and true supplemental sources precede typed private task windows. -/
structure BeforeTasks where
  /-- First address available after the earlier geometry and receive banks. -/
  start : ℕ
  /-- Length-only maxima. -/
  bound : Bounds

/-- One width word per global cell. -/
def BeforeTasks.tailWidths (a : BeforeTasks) := a.start

/-- Reserved contiguous supplemental row stream of every global cell. -/
def BeforeTasks.supplement (a : BeforeTasks) := a.tailWidths+a.bound.cells

/-- Two returned scalar counters per global cell. -/
def BeforeTasks.counters (a : BeforeTasks) := a.supplement+a.bound.cells*a.bound.supplementStride

/-- Merged count scratch for typed calls. -/
def BeforeTasks.merged (a : BeforeTasks) := a.counters+2*a.bound.cells

/-- Compact four-word supplemental headers for the owned cells. -/
def BeforeTasks.four (a : BeforeTasks) := a.merged+a.bound.cells

/-- Independent six-word scanner headers for the owned cells. -/
def BeforeTasks.six (a : BeforeTasks) := a.four+4*a.bound.cells

/-- Two first/past bundle ordinals per global cell. -/
def BeforeTasks.ranges (a : BeforeTasks) := a.six+6*a.bound.cells

/-- The stable six-word list of genuine bottom bundles. -/
def BeforeTasks.bundleTable (a : BeforeTasks) := a.ranges+2*a.bound.cells

/-- First free word for later typed task windows. -/
def BeforeTasks.limit (a : BeforeTasks) := a.bundleTable+6*a.bound.bundles

/-- The exact pre-task footprint includes only address reservations; the program
writes the actual headers and rows counted in its sparse tick bounds. -/
theorem BeforeTasks.footprint (a : BeforeTasks) : a.limit =
    a.start+16*a.bound.cells+a.bound.cells*a.bound.supplementStride+6*a.bound.bundles := by
  simp [limit,bundleTable,ranges,six,four,merged,counters,supplement,tailWidths]; ring

/-- The lookup and tally partitions start after the typed call windows, earlier packet
vertex triples and immutable finite cube tables. -/
structure AfterTasks where
  /-- First fresh address after all previous input banks. -/
  start : ℕ
  /-- Length-only maxima. -/
  bound : Bounds

/-- Two begin/end reference words for each owned vertex. -/
def AfterTasks.lookupRows (a : AfterTasks) := a.start

/-- Gather references to actual incident physical packet bits. -/
def AfterTasks.lookupRefs (a : AfterTasks) := a.lookupRows+2*a.bound.vertices

/-- One chosen cube table ID per owned vertex. -/
def AfterTasks.ids (a : AfterTasks) := a.lookupRefs+a.bound.vertices*a.bound.cubeWidth

/-- The real packed count and three-word metadata rows for each original bundle. -/
def AfterTasks.packed (a : AfterTasks) := a.ids+a.bound.vertices+1

/-- Actual physical bit references for cell count and use operands. -/
def AfterTasks.refs (a : AfterTasks) := a.packed+a.bound.bundles*(1+3*a.bound.marked)+1

/-- The five-word descriptor array, also reserving the subsequent cube suffix. -/
def AfterTasks.descriptors (a : AfterTasks) :=
  a.refs+(a.bound.cells*a.bound.gadgets*a.bound.countWidth+a.bound.uses)+1

/-- Upper bound for the true cell-plus-cube operand count. -/
def Bounds.operands (b : Bounds) := b.cells*b.gadgets+b.uses+b.vertices

/-- Lowest permitted start of the generated scatter records. -/
def AfterTasks.fresh (a : AfterTasks) := a.descriptors+5*a.bound.operands+1

/-- Fixed address of the local subtotal bank, independently of the actual count.
The compiled alignment routine puts the generated records immediately before it. -/
def AfterTasks.localBase (a : AfterTasks) := a.fresh+2*a.bound.operands

/-- Exact tail allocation size before dynamic tally evaluation. Gaps separate source
words and output cursors even at degenerate dimensions. -/
theorem AfterTasks.footprint (a : AfterTasks) : a.fresh=a.start+4+3*a.bound.vertices+
    a.bound.vertices*a.bound.cubeWidth+a.bound.bundles*(1+3*a.bound.marked)+
    a.bound.cells*a.bound.gadgets*a.bound.countWidth+a.bound.uses+5*a.bound.operands := by
  simp [fresh,descriptors,refs,packed,ids,lookupRefs,lookupRows]; ring

/-- The pre-task reservations supply exactly the listed task/geometry control fields.
Other independently installed control scalars are read from the underlying layout. -/
def BeforeTasks.controls (a : BeforeTasks) (previous : ℕ → ℕ) : ℕ → ℕ
  | 7 => a.tailWidths | 11 => a.four | 12 => a.supplement | 13 => a.bound.supplementStride
  | 14 => a.counters | 15 => a.merged | 16 => 1+a.bound.gadgets*(1+a.bound.countWidth)
  | 17 => a.six | 18 => a.ranges | 19 => a.bundleTable | i => previous i

/-- The six post-task supplemental input controls are length-only scalar words. -/
def AfterTasks.controls (a : AfterTasks) (fieldWidth bodyCap : ℕ) (previous : ℕ → ℕ) : ℕ → ℕ
  | 22 => a.bound.countWidth | 23 => fieldWidth | 24 => bodyCap | 25 => a.packed
  | 26 => a.refs | 27 => a.bound.gadgets | i => previous i

/-- The post-task frame pointers share the existing vertex triples in slot 78 and the
immutable recipe, ID lookup, and literal addresses already installed by cube setup. -/
def AfterTasks.frameFields (a : AfterTasks) (previous : ℕ → ℕ) : ℕ → ℕ
  | 34 => a.localBase | 44 => a.descriptors | 45 => a.lookupRows | 71 => a.ids
  | 80 => a.lookupRefs | i => previous i

/-- One scalar ceiling suffices for the allocation proof; separately bounded geometric
dimensions retain their own concrete values in the actual address formulas. -/
structure Bounds.Le (b : Bounds) (K : ℕ) : Prop where
  /-- Global cell count. -/
  cells : b.cells ≤ K
  /-- Retained bottom-bundle count. -/
  bundles : b.bundles ≤ K
  /-- Maximum one-copy marked count. -/
  marked : b.marked ≤ K
  /-- Actual expanded marked-copy ceiling. -/
  uses : b.uses ≤ K
  /-- Gadget alphabet cardinality. -/
  gadgets : b.gadgets ≤ K
  /-- Count bit width. -/
  countWidth : b.countWidth ≤ K
  /-- Owned-vertex ceiling. -/
  vertices : b.vertices ≤ K
  /-- Fixed lookup digit width. -/
  cubeWidth : b.cubeWidth ≤ K
  /-- Per-cell supplemental address stride. -/
  supplementStride : b.supplementStride ≤ K

/-- Pre-task geometry/control allocation fits a fixed polynomial in the common length ceiling. -/
theorem BeforeTasks.polynomial_room (a : BeforeTasks) {K : ℕ} (h : a.bound.Le K) :
    a.limit ≤ a.start+23*(K+1)^2 := by
  rw [a.footprint]
  have prod := Nat.mul_le_mul h.cells h.supplementStride
  nlinarith [h.cells,h.bundles]

/-- The complete lookup/metadata/operand partition has a fixed cubic bound independent
of the profile and private assignment. -/
theorem AfterTasks.polynomial_room (a : AfterTasks) {K : ℕ} (h : a.bound.Le K) :
    a.fresh ≤ a.start+32*(K+1)^3 := by
  rw [a.footprint]
  unfold Bounds.operands
  have lu := Nat.mul_le_mul h.vertices h.cubeWidth
  have pm := Nat.mul_le_mul h.bundles (show 1+3*a.bound.marked ≤ 1+3*K by have := h.marked; omega)
  have cg := Nat.mul_le_mul h.cells h.gadgets
  have cw := Nat.mul_le_mul cg h.countWidth
  nlinarith [h.vertices,h.uses]

end DiagonalTallyAllocation

end BorderVNP
end Computability
end OAI
