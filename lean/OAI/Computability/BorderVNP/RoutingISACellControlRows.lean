import OAI.Computability.BorderVNP.RoutingISATypedTaskMemory

/-! # Native cell headers for the weighted sidecar scan and supplemental descriptor writer

The six-word sidecar header is available before any private report multiplicity
is read. Its two range ends refer to the true sorted original-bundle array.
The companion four-word row names the supplemental stream, counters and merged
record count. Both arrays use exactly the task builder's global ownership order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellControlRows

open TypedTaskBuilder Packing.Directory.ISA VPVNP.BurstRAM

/-- Fixed scalar header fields, supplementing the base task-builder allocation. -/
structure Layout extends TypedTaskBuilder.Layout where
  /-- Number of grouped live port rows before the per-cell private end column. -/
  ports : ℕ
  /-- Pointer in frame word 65 to those two-word live port rows. -/
  live : ℕ
  /-- Compact four-word supplemental control table. -/
  four : ℕ
  /-- Per-cell supplemental stream arena. -/
  supplemental : ℕ
  /-- Reserved supplemental stream words per cell. -/
  stride : ℕ
  /-- Two actual counters per cell, record count followed by encoded word count. -/
  counters : ℕ
  /-- One scratch word per cell for the merged count. -/
  merged : ℕ
  /-- Actual length of the uniform public list of gadget subtotal address vectors. -/
  reportWords : ℕ
  /-- Compact six-word original-site sidecar header table. -/
  six : ℕ
  /-- True first and past bundle ordinals per global cell from the public geometry sort. -/
  ranges : ℕ

/-- Four operands for the sparse typed packet supplemental writer. -/
def Layout.rowFour (l : Layout) (c : ℕ) : List ℕ :=
  [l.supplemental+l.stride*c,l.counters+2*c,l.merged+c,l.reportWords]

/-- Six operands for the actual owned-cell original-bundle scan. -/
def Layout.rowSix (l : Layout) (mem : ℕ → ℕ) (c : ℕ) : List ℕ :=
  [c,mem (l.banks+2*c+1),mem (l.offsets+2*l.cables+c),mem (l.live+2*l.ports+c),
    mem (l.ranges+2*c),mem (l.ranges+2*c+1)]

/-- Public outer and indirect fields read by the fused producer. -/
structure Layout.Fields (l : Layout) (mem : ℕ → ℕ) : Prop where
  /-- Ownership, real cell directory, and placement array pointers. -/
  frame : mem l.frame=l.team ∧ mem (l.frame+15)=l.cells ∧ mem (l.frame+72)=l.banks ∧
    mem (l.frame+87)=l.offsets ∧ mem (l.frame+7)=l.cables ∧ mem (l.frame+65)=l.live ∧
    mem (l.frame+1)*mem (l.frame+67)=l.ports ∧ mem (l.frame+92)=l.control
  /-- Frame-92 header words 11 through 18. -/
  control : mem (l.control+11)=l.four ∧ mem (l.control+12)=l.supplemental ∧
    mem (l.control+13)=l.stride ∧ mem (l.control+14)=l.counters ∧ mem (l.control+15)=l.merged ∧
    mem (l.control+16)=l.reportWords ∧ mem (l.control+17)=l.six ∧ mem (l.control+18)=l.ranges

/-- Physical input words consulted during one global-cell iteration. -/
def Layout.inputs (l : Layout) (c a : ℕ) : Prop :=
  a=l.banks+2*c ∨ a=l.banks+2*c+1 ∨ a=l.offsets+2*l.cables+c ∨ a=l.live+2*l.ports+c ∨
    a=l.ranges+2*c ∨ a=l.ranges+2*c+1

/-- Address spans written by the two compact control tables or their common count. -/
def Layout.outputs (l : Layout) (a : ℕ) : Prop :=
  (l.four ≤ a ∧ a < l.four+4*l.cells) ∨ (l.six ≤ a ∧ a < l.six+6*l.cells) ∨ a=l.frame+90

/-- Word bounds and disjoint live memory ranges. -/
structure Layout.Room (l : Layout) (w : ℕ) : Prop where
  /-- The two true scalar headers. -/
  frame : l.frame+112 < 2^w ∧ l.control+19 < 2^w
  /-- End of the four live input arrays. -/
  input : l.banks+2*l.cells < 2^w ∧ l.offsets+2*l.cables+l.cells < 2^w ∧
    l.live+2*l.ports+l.cells < 2^w ∧ l.ranges+2*l.cells < 2^w
  /-- End of the two returned tables. -/
  result : l.four+4*l.cells < 2^w ∧ l.six+6*l.cells < 2^w
  /-- Reserved supplement, counter, and merged-count addresses. -/
  fields : l.supplemental+l.stride*l.cells < 2^w ∧ l.counters+2*l.cells < 2^w ∧ l.merged+l.cells < 2^w
  /-- Reads of live control data never alias the two populated output arrays. -/
  inputApart : ∀ c < l.cells, ∀ a, l.inputs c a → ¬l.outputs a
  /-- Compact tables are disjoint and lie after the frame. -/
  outputApart : (l.four+4*l.cells ≤ l.six ∨ l.six+6*l.cells ≤ l.four) ∧ l.frame+112 ≤ l.four ∧ l.frame+112 ≤ l.six

/-- Memory after processing the cells before the cursor. -/
def Layout.image (l : Layout) (mem : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => mem
  | c+1 =>
    if l.owner mem c=l.team then
      let j := l.before mem c
      let z := putNat (l.image mem c) (l.six+6*j) (l.rowSix mem c)
      putNat z (l.four+4*j) (l.rowFour c)
    else l.image mem c

/-- The common populated count is written into frame word 90. -/
def Layout.published (l : Layout) (mem : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (l.image mem l.cells) (l.frame+90) (l.before mem l.cells)

private def indirect (r : Reg) (k : Word 8) : Code :=
  .block [.constant 63 k,.binary .add 62 61 63,.load r 62]

/-- Fetch the shared bases and initialize the global and compact ordinals. -/
def setup : Code := .block [
  .constant 0 0,.constant 1 1,.constant 2 2,.constant 3 4,.constant 4 6,
  readFrame 5 62 63 0,readFrame 6 62 63 15,readFrame 7 62 63 72,
  readFrame 8 62 63 87,readFrame 60 62 63 7,.binary .mul 60 2 60,.binary .add 8 8 60,
  readFrame 9 62 63 65,readFrame 59 62 63 1,readFrame 60 62 63 67,.binary .mul 60 59 60,
  .binary .mul 60 2 60,.binary .add 9 9 60,
  readFrame 61 62 63 92,indirect 10 18,indirect 11 11,indirect 12 12,indirect 13 13,
  indirect 14 14,indirect 15 15,indirect 16 16,indirect 17 17,.copy 18 0,.copy 19 0]

/-- Read the real cell, its range of original bundles, and the four fixed supplemental operands. -/
def gather : Code := .block [
  .copy 22 18,.binary .mul 32 2 18,.binary .add 33 7 32,.load 21 33,
  .binary .add 33 33 1,.load 23 33,.binary .add 33 8 18,.load 24 33,.binary .add 33 9 18,.load 25 33,
  .binary .add 33 10 32,.load 26 33,.binary .add 33 33 1,.load 27 33,
  .binary .mul 28 13 18,.binary .add 28 12 28,.binary .add 29 14 32,.binary .add 30 15 18,.copy 31 16]

/-- Set the current compact output cursor and copy one fixed group of fields. -/
def pushAt (stride base : Reg) (rs : List Reg) : Code :=
  .seq (.block [.binary .mul 20 stride 19,.binary .add 20 base 20]) (pushWords rs)

/-- Write both compact owned rows, advancing the local cursor once. -/
def emit : Code :=
  .seq (pushAt 4 17 [22,23,24,25,26,27]) (.seq (pushAt 3 11 [28,29,30,31]) (.binary .add 19 19 1))

/-- One iteration always advances its public cell cursor. -/
def commit : Code := .seq (.ifEq 21 5 emit .nop) (.binary .add 18 18 1)

/-- One gather followed by the ownership branch. -/
def body : Code := .seq gather commit

/-- Return the actual compact owned-cell count to the shared frame. -/
def finish : Code := .block [.publicWord 62 0,.constant 63 90,.binary .add 62 62 63,.store 62 19]

/-- Complete deterministic pre-sidecar producer. -/
def program : Code := .seq setup (.seq (.whileLt 18 6 body) finish)

/-- The nineteen controls and the compact row count in the twenty low registers. -/
def Layout.regValue (l : Layout) (i j : ℕ) (r : Reg) : ℕ :=
  [0,1,2,4,6,l.team,l.cells,l.banks,l.offsets+2*l.cables,l.live+2*l.ports,l.ranges,
    l.four,l.supplemental,l.stride,l.counters,l.merged,l.reportWords,l.six,i,j].getD r.val 0

/-- Low registers at a global-cell boundary. -/
def Layout.Ready (l : Layout) (i j : ℕ) (z : NatState) : Prop :=
  ∀ r : Reg, r.val < 20 → z.reg r=l.regValue i j r

end RoutingISA.CellControlRows

end BorderVNP
end Computability
end OAI
