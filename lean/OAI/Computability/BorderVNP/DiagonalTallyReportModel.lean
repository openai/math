import OAI.Computability.BorderVNP.DiagonalTallyReportBundle
import OAI.Computability.BorderVNP.PackedBottomBundleHeader

/-! # Compact cells, their chronological report bits and the emitted operand order -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM TallySidecar DiagonalTallyMaterialize
open Packing.BottomReports

/-- Addresses and fixed field dimensions supplied to the owner's traversal. -/
structure ReportLayout where
  /-- Public frame address. -/
  frame : ℕ
  /-- Frame-92 control subdirectory. -/
  control : ℕ
  /-- Beginning of the six-word owned-cell headers. -/
  headers : ℕ
  /-- Beginning of the globally grouped six-word bottom bundle headers. -/
  bundleTable : ℕ
  /-- Number of parameter coordinates before the gadget counts. -/
  parameters : ℕ
  /-- Number of possible gadget IDs, fixed with the shortening identity. -/
  gadgets : ℕ
  /-- Per-gadget count bit width. -/
  countWidth : ℕ
  /-- Scalar width of the delivered private sidecar metadata. -/
  fieldWidth : ℕ
  /-- Reserved one-copy box body length before the separate sidecar. -/
  bodyCap : ℕ
  /-- Address of the literal zero word. -/
  zeroAddr : ℕ
  /-- Tail-width output words indexed by genuine global cell. -/
  tailWidths : ℕ
  /-- Reserved supplemental checker-row arena. -/
  supplement : ℕ
  /-- Address stride of that arena between global cells. -/
  supplementStride : ℕ
  /-- Address of the two supplemental counters per global cell. -/
  counters : ℕ

/-- Persistent physical output cursors across owned cells. -/
structure ReportCursor where
  /-- First unused packed metadata word. -/
  packed : ℕ
  /-- First unused five-word descriptor position. -/
  descriptors : ℕ
  /-- First unused indirect bit-address word. -/
  refs : ℕ
  /-- Number of complete operands already emitted. -/
  prior : ℕ

/-- One immutable site description, its public clone geometry, and the prescribed
use bits of the currently considered expanded assignment. -/
structure ReportBundle where
  /-- The six public physical operands read from the retained-site traversal. -/
  header : BundleHeader
  /-- The actual original factor description in the opaque box prefix. -/
  factors : List CellSparse.Factor
  /-- Listed weighted positions, with immutable one-copy relative staging lanes. -/
  positions : List Position
  /-- One true/false choice for each listed position and each copy, in that order. -/
  uses : Fin (positions.length*header.copies) → Bool

/-- An owned cell and the reports physically guessed before its private call. -/
structure ReportCell (l : ReportLayout) where
  /-- Global cell number in the prepared owned row. -/
  number : ℕ
  /-- Absolute RAM address of the cell's supplied words. -/
  external : ℕ
  /-- Number of original supplied words before the supplement. -/
  supplied : ℕ
  /-- Number of private wires before the supplied wires in the private assignment. -/
  privateWires : ℕ
  /-- First ordinal in the stable globally grouped bottom-bundle array. -/
  first : ℕ
  /-- The cell's actual retained bottom bundles in their native order. -/
  bundles : List ReportBundle
  /-- Checked gadget fields, little-endian per coordinate. -/
  counts : Fin l.gadgets → Fin l.countWidth → Bool

/-- The owned-cell ABI contains every cell, including an empty original-bundle range. -/
def ReportCell.headerWords {l : ReportLayout} (c : ReportCell l) : List ℕ :=
  [c.number,c.external,c.supplied,c.privateWires,c.first,c.first+c.bundles.length]

/-- Number of actual weighted-use bits in this bottom bundle. -/
def ReportBundle.useCount (b : ReportBundle) := b.positions.length*b.header.copies

/-- The exact compact choice stream, with each reported bit guessed once. -/
def ReportCell.bits {l : ReportLayout} (c : ReportCell l) : List Bool :=
  (List.ofFn fun g => List.ofFn (c.counts g)).flatten ++ c.bundles.flatMap (fun b => List.ofFn b.uses)

/-- Exact count-and-use width supplied to the typed task row builder. -/
def ReportCell.tailWidth {l : ReportLayout} (c : ReportCell l) : ℕ :=
  l.gadgets*l.countWidth+(c.bundles.map ReportBundle.useCount).sum

theorem ReportCell.bits_length {l : ReportLayout} (c : ReportCell l) : c.bits.length=c.tailWidth := by
  simp [bits,tailWidth,List.length_flatten,List.map_ofFn,
    Function.comp_def,List.ofFn_const]
  rfl

/-- The per-cell count writer starts immediately after the original supplied inputs. -/
def ReportCell.countFrame {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) :
    DiagonalTallyOperandArray.Frame :=
  ⟨l.parameters,l.gadgets,l.countWidth,l.zeroAddr,q.packed,0,0,c.external+c.supplied,
    q.descriptors,q.refs,q.prior⟩

/-- A bundle's unary writer uses that site's decoded metadata and the current physical cursors. -/
def ReportBundle.frame (l : ReportLayout) (b : ReportBundle) (q : ReportCursor) (external : ℕ) :
    DiagonalTallyOperandArray.Frame :=
  ⟨l.parameters,l.gadgets,l.countWidth,l.zeroAddr,q.packed,b.positions.length,b.header.copies,
    external,q.descriptors,q.refs,q.prior⟩

/-- Reserve just the emitted words after the gadget block. -/
def ReportCursor.afterCounts (q : ReportCursor) (l : ReportLayout) : ReportCursor :=
  ⟨q.packed,q.descriptors+5*l.gadgets,q.refs+l.gadgets*l.countWidth,q.prior+l.gadgets⟩

/-- Reserve the count header, three fields per mark, and one operand per actual marked copy. -/
def ReportCursor.afterBundle (q : ReportCursor) (b : ReportBundle) : ReportCursor :=
  ⟨q.packed+1+3*b.positions.length,q.descriptors+5*b.useCount,q.refs+b.useCount,q.prior+b.useCount⟩

/-- The immutable source of the given flattened position/copy occurrence. -/
def ReportBundle.source (b : ReportBundle) (i : Fin b.useCount) : Position :=
  b.positions[i.val/b.header.copies]'(by
    have hi := i.isLt
    change i.val<b.positions.length*b.header.copies at hi
    have hp : 0<b.header.copies := by
      by_contra! hz
      have e : b.header.copies=0 := by omega
      simp [e] at hi
    exact (Nat.div_lt_iff_lt_mul hp).mpr hi)

/-- A real emitted use row, with the address of the source parameter and exponent, its
own report bit and the corresponding binary increment. -/
def ReportBundle.operand (b : ReportBundle) (q : ReportCursor) (external : ℕ) (i : Fin b.useCount) :
    Operand :=
  let a := q.packed+3*(i.val/b.header.copies)+1
  unaryOperand a (a+1) (q.refs+i.val) (external+i.val) (b.source i).parameter (b.source i).place (b.uses i)

/-- All chronological uses for the grouped bottom bundles, retaining exact physical addresses. -/
def bundleOperands : List ReportBundle → ReportCursor → ℕ → List Operand
  | [],_,_ => []
  | b::bs,q,a => List.ofFn (b.operand q a) ++ bundleOperands bs (q.afterBundle b) (a+b.useCount)

/-- The actual descriptor order of one owned cell, before the final cube suffix. -/
def ReportCell.operands {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) : List Operand :=
  (List.ofFn fun g => (c.countFrame q).countRow g (c.counts g)) ++
    bundleOperands c.bundles (q.afterCounts l) (c.external+c.supplied+l.gadgets*l.countWidth)

/-- The next owned cell inherits precisely the four advanced global cursors. -/
def ReportCell.after {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) : ReportCursor :=
  c.bundles.foldl ReportCursor.afterBundle (q.afterCounts l)

/-- The physical operand list of all owned cells in native order. -/
def cellOperands {l : ReportLayout} : List (ReportCell l) → ReportCursor → List Operand
  | [],_ => []
  | c::cs,q => c.operands q ++ cellOperands cs (c.after q)

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
