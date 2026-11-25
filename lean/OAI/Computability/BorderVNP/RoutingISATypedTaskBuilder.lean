import OAI.Computability.BorderVNP.RoutingISATypedBatchEntry
import OAI.Computability.BorderVNP.RoutingISATableSetup
import OAI.Computability.BorderVNP.PackedDirectoryISA

/-! # Native producer of the compact owned-cell task table

All teams reconstruct the same sparse cell order. A team writes each call's
public owner column, but emits the seven initializer words only for its own
cells. The descriptor bases and ends are two actual inverse-sort lookups.
The live external buffer and its bit length come from the cell-bank directory
and the compiled compact assignment allocation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedTaskBuilder

open VPVNP.BurstRAM Packing.Directory.ISA

/-- Public bases for one execution of the cell-task producer. -/
structure Layout where
  /-- Start of the extended shared frame. -/
  frame : ℕ
  /-- Identity of the executing team. -/
  team : ℕ
  /-- Number of public cell rows. -/
  cells : ℕ
  /-- Number of public cable slots preceding the supplied-width section. -/
  cables : ℕ
  /-- Start of the global three-word owner/call directory. -/
  calls : ℕ
  /-- Start of the two-word owner and supplied-bank rows. -/
  banks : ℕ
  /-- Start of the combined endpoint-offset and supplied-width output. -/
  offsets : ℕ
  /-- Start of this team's compact seven-word initializer task directory. -/
  tasks : ℕ
  /-- Pointer in frame word 92 to the eight fixed allocation parameters. -/
  control : ℕ
  /-- Start of the sorted descriptor word output. -/
  sorted : ℕ
  /-- Padded number of descriptor words, preceding their inverse row ordinals. -/
  padded : ℕ
  /-- Raw ordinal of the first stop marker, after cell starts and all chunk words. -/
  stops : ℕ
  /-- Temporary bit arena for the packet builder. -/
  scratch : ℕ
  /-- Arena of compact bursts retained until the dispatch pass. -/
  bursts : ℕ
  /-- Reserved address span between two scratch starts. -/
  scratchStride : ℕ
  /-- Reserved address span between two burst starts. -/
  burstStride : ℕ
  /-- Array of actual compact report/use tail lengths produced for these cells. -/
  tails : ℕ

/-- Current owner selected by the physical two-word placement table. -/
def Layout.owner (l : Layout) (mem : ℕ → ℕ) (c : ℕ) := mem (l.banks+2*c)

/-- Start of the output owner, argument-address and word-length triple. -/
def Layout.call (l : Layout) (c : ℕ) := l.calls+3*c

/-- The seven task words consumed by the private packet initializer. -/
def Layout.row (l : Layout) (mem : ℕ → ℕ) (c : ℕ) : List ℕ :=
  let inv := l.sorted+l.padded
  [l.sorted+mem (inv+c)+1, l.sorted+mem (inv+(l.stops+c)), mem (l.banks+2*c+1),
    mem (l.offsets+2*l.cables+c)+mem (l.tails+c), l.scratch+l.scratchStride*c,
    l.bursts+l.burstStride*c, l.call c]

/-- Number of owned tasks strictly before the named global cell. -/
def Layout.before (l : Layout) (mem : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | c+1 => l.before mem c + if l.owner mem c = l.team then 1 else 0

/-- Each of the first cells contributes at most one task. -/
theorem Layout.before_le (l : Layout) (mem : ℕ → ℕ) (c : ℕ) : l.before mem c ≤ c := by
  induction c with
  | zero => rfl
  | succ i ih => simp only [before]; split <;> omega

/-- Addresses used to read current ownership, supplied bit length and the two sorted markers. -/
def Layout.inputAt (l : Layout) (c a : ℕ) : Prop :=
  a = l.banks+2*c ∨ a = l.banks+2*c+1 ∨ a = l.offsets+2*l.cables+c ∨
  a = l.sorted+l.padded+c ∨ a = l.sorted+l.padded+(l.stops+c) ∨ a = l.tails+c

/-- Every store of the task directory, owner columns, or final task count. -/
def Layout.outputAt (l : Layout) (a : ℕ) : Prop :=
  (l.tasks ≤ a ∧ a < l.tasks+7*l.cells) ∨ (∃ c < l.cells, a = l.call c) ∨ a = l.frame+90

/-- The actual frame words and the fixed task-builder allocation header. -/
structure Layout.Fields (l : Layout) (mem : ℕ → ℕ) : Prop where
  /-- Frame entries supplied by the placement, bank and call stages. -/
  outer : mem l.frame=l.team ∧ mem (l.frame+7)=l.cables ∧ mem (l.frame+14)=l.calls ∧
    mem (l.frame+15)=l.cells ∧ mem (l.frame+72)=l.banks ∧ mem (l.frame+87)=l.offsets ∧
    mem (l.frame+89)=l.tasks ∧ mem (l.frame+92)=l.control
  /-- The eight allocation words at the indirect control base. -/
  header : mem l.control=l.sorted ∧ mem (l.control+1)=l.padded ∧ mem (l.control+2)=l.stops ∧
    mem (l.control+3)=l.scratch ∧ mem (l.control+4)=l.bursts ∧
    mem (l.control+5)=l.scratchStride ∧ mem (l.control+6)=l.burstStride ∧ mem (l.control+7)=l.tails

/-- Numerical room for all native address arithmetic and separation of task rows from sources. -/
structure Layout.Room (l : Layout) (mem : ℕ → ℕ) (w : ℕ) : Prop where
  /-- Header addresses and constants fit the machine word. -/
  frame : l.frame+112 < 2^w
  /-- The indirect header is readable. -/
  control : l.control+8 < 2^w
  /-- End of the owner/call triples. -/
  calls : l.calls+3*l.cells < 2^w
  /-- End of the two-word owner/bank table. -/
  banks : l.banks+2*l.cells < 2^w
  /-- End of the supplied bit count array. -/
  offsets : l.offsets+2*l.cables+l.cells < 2^w
  /-- All per-cell tail extent words are addressable. -/
  tails : l.tails+l.cells < 2^w
  /-- The supplied width and measured report tail fit on each owned cell. -/
  external : ∀ c < l.cells, l.owner mem c = l.team → mem (l.offsets+2*l.cables+c)+mem (l.tails+c) < 2^w
  /-- One-past-the-end of the compact task table even if every cell belongs to this team. -/
  tasks : l.tasks+7*l.cells < 2^w
  /-- Both descriptor arrays fit the machine word. -/
  sorted : l.sorted+2*l.padded < 2^w
  /-- Start and stop markers are actual rows in the inverse descriptor array. -/
  markers : l.cells ≤ l.stops ∧ l.stops+l.cells ≤ l.padded
  /-- Returned descriptor marker ranks lie in the padded array. -/
  ranks : ∀ c < l.cells, mem (l.sorted+l.padded+c) < l.padded ∧
    mem (l.sorted+l.padded+(l.stops+c)) < l.padded
  /-- Allocated scratch starts fit for all cells. -/
  scratch : l.scratch+l.scratchStride*l.cells < 2^w
  /-- Allocated burst starts fit for all cells. -/
  bursts : l.bursts+l.burstStride*l.cells < 2^w
  /-- Every future read of the cell scan is disjoint from the task producer's stores. -/
  input : ∀ c < l.cells, ∀ a, l.inputAt c a → ¬l.outputAt a
  /-- Owner columns and the frame stay outside the compact task table. -/
  ownerTasks : l.calls+3*l.cells ≤ l.tasks ∨ l.tasks+7*l.cells ≤ l.calls
  /-- The frame stays outside both populated output arrays. -/
  outputs : l.frame+112 ≤ l.calls ∧ l.frame+112 ≤ l.tasks

/-- Fixed small indirect header loads, using register 61 as the control pointer. -/
private def controlWord (r : Reg) (f : Word 8) : Code :=
  .block [.constant 63 f, .binary .add 62 61 63, .load r 62]

/-- Fetch the immutable shared frame and header, and initialize both row cursors. -/
def setup : Code := .block [
  .constant 0 0,.constant 1 1,.constant 2 2,.constant 3 3,
  readFrame 4 62 63 0,readFrame 5 62 63 15,readFrame 6 62 63 14,
  readFrame 7 62 63 72,readFrame 8 62 63 87,readFrame 60 62 63 7,
  .binary .mul 60 2 60,.binary .add 8 8 60,
  readFrame 61 62 63 92,controlWord 9 0,controlWord 10 1,.binary .add 10 9 10,
  controlWord 11 2,controlWord 12 3,controlWord 13 4,controlWord 14 5,controlWord 15 6,
  readFrame 16 62 63 89,.publicWord 17 0,.constant 63 90,.binary .add 17 17 63,
  .copy 18 0,.copy 19 0,controlWord 0 7]

/-- Resolve all word fields from the original sparse placement and sorted output.
Only an owned cell combines its supplied width and report tail. The owner is register 21, the task write pointer is 20, and the task words are 24 through 30. -/
def gather : Code := .block [
  .constant 20 7,.binary .mul 20 20 19,.binary .add 20 16 20,
  .binary .mul 31 2 18,.binary .add 31 7 31,.load 21 31,.binary .add 31 31 1,.load 26 31,
  .binary .add 31 10 18,.load 24 31,.binary .add 24 9 24,.binary .add 24 24 1,
  .binary .add 31 11 18,.binary .add 31 10 31,.load 25 31,.binary .add 25 9 25,
  .binary .add 31 8 18,.load 27 31,.binary .add 31 0 18,.load 32 31,
  .ifEq 21 4 (.binary .add 27 27 32) .nop,
  .binary .mul 28 14 18,.binary .add 28 12 28,.binary .mul 29 15 18,.binary .add 29 13 29,
  .binary .mul 30 3 18,.binary .add 30 6 30]

/-- Write a populated seven-word row, then advance the owned-row cursor. -/
def emit : Code := .seq (pushWords [24,25,26,27,28,29,30]) (.binary .add 19 19 1)

/-- Store the selected words and advance the global cell counter. -/
def commitRow : Code := .seq (.store 30 21) (.seq (.ifEq 21 4 emit .nop) (.binary .add 18 18 1))

/-- Publish the global owner and emit the local task exactly for its designated team. -/
def body : Code := .seq gather commitRow

/-- The owner-filtered task producer, including publication of frame word 90. -/
def program : Code := .seq setup (.seq (.whileLt 18 5 body) (.store 17 19))

/-- The first twenty register readings at the boundary of a loop iteration. -/
def Layout.regValue (l : Layout) (i j : ℕ) (r : Reg) : ℕ :=
  [l.tails,1,2,3,l.team,l.cells,l.calls,l.banks,l.offsets+2*l.cables,l.sorted,
    l.sorted+l.padded,l.stops,l.scratch,l.bursts,l.scratchStride,l.burstStride,
    l.tasks,l.frame+90,i,j].getD r.val 0

/-- Values surviving until the next row and the two current row counters. -/
def Layout.Ready (l : Layout) (i j : ℕ) (z : NatState) : Prop :=
  ∀ r : Reg, r.val < 20 → z.reg r = l.regValue i j r

end RoutingISA.TypedTaskBuilder

end BorderVNP
end Computability
end OAI
