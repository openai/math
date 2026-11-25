import OAI.Computability.BorderVNP.RoutingISATableState

/-! # Sparse incidence directories for the public label chooser (§8.1)

The input consists of three-word oriented cables and seven-word deliveries. Two
four-word incidence nodes are reserved per cable. A node stores the previous head,
orientation, opposite endpoint and full width. Zero is the empty list and node
ordinal `j` is referenced by `j+1`. Per-cell data demand is aggregated in one
word. Both mean tables use denominator `Z²`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open RoutingISA VPVNP.BurstRAM

/-- Addressed input and output arrays of the chooser. -/
structure Layout where
  /-- Oriented cable triples. -/
  cables : ℕ
  /-- Cable count. -/
  cableCount : ℕ
  /-- Seven-word delivery rows. -/
  deliveries : ℕ
  /-- Delivery count. -/
  deliveryCount : ℕ
  /-- Number of cells in public order. -/
  cells : ℕ
  /-- Per-cell incidence heads. -/
  heads : ℕ
  /-- Four-word incidence nodes. -/
  nodes : ℕ
  /-- Per-cell total delivery width. -/
  data : ℕ
  /-- Ordered-pair cable mean numerators. -/
  cableMean : ℕ
  /-- Per-label data mean numerators. -/
  dataMean : ℕ
  /-- Number of labels. -/
  labels : ℕ

/-- Decode the words used by the reconstruction and chooser. -/
def layout (frame : ℕ) (m : ℕ → ℕ) : Layout :=
  let f j := m (frame+j)
  ⟨f 6,f 7,f 8,f 9,f 11,f 49,f 50,f 51,f 52,f 53,f 56⟩

/-- A persistent sparse-list insertion in the natural memory model. -/
def push (m : ℕ → ℕ) (heads nodes ordinal cell dir other width : ℕ) : ℕ → ℕ :=
  let b := nodes+ordinal*4
  let h := heads+cell
  Function.update (Function.update (Function.update (Function.update
    (Function.update m b (m h)) (b+1) dir) (b+2) other) (b+3) width) h (ordinal+1)

/-- Working memory and the two original total volumes. -/
structure Acc where
  /-- Sparse directory in ordinary addressed memory. -/
  mem : ℕ → ℕ
  /-- Cumulative cable volume. -/
  cableTotal : ℕ
  /-- Cumulative data volume. -/
  dataTotal : ℕ

/-- The five passes of the directory builder. -/
inductive Phase where
  | clear | cable | delivery | cableBins | dataBins
  deriving DecidableEq

/-- Number of rows scanned in each pass. -/
def Phase.count (l : Layout) : Phase → ℕ
  | .clear => l.cells
  | .cable => l.cableCount
  | .delivery => l.deliveryCount
  | .cableBins => l.labels*l.labels
  | .dataBins => l.labels

/-- One reference row, reading its actual input columns and writing only its
heads, nodes, demand, or initial means. -/
def Phase.step (p : Phase) (l : Layout) (i : ℕ) (a : Acc) : Acc :=
  let m := a.mem
  match p with
  | .clear => { a with mem := Function.update (Function.update m (l.heads+i) 0) (l.data+i) 0 }
  | .cable =>
    let b := l.cables+i*3
    let x := m b
    let y := m (b+1)
    let d := m (b+2)
    let m' := push m l.heads l.nodes (i*2) x 0 y d
    if x = y then a else { a with mem := push m' l.heads l.nodes (i*2+1) y 1 x d, cableTotal := a.cableTotal+d }
  | .delivery =>
    let b := l.deliveries+i*7
    let dest := l.data+m (b+4)
    let d := m (b+6)
    { a with mem := Function.update m dest (m dest+d), dataTotal := a.dataTotal+d }
  | .cableBins => { a with mem := Function.update m (l.cableMean+i) a.cableTotal }
  | .dataBins => { a with mem := Function.update m (l.dataMean+i) (a.dataTotal*l.labels) }

/-- Memory and volumes after a prefix of a pass. -/
def Phase.prefix (p : Phase) (l : Layout) (a : Acc) : ℕ → Acc
  | 0 => a
  | i+1 => p.step l i (p.prefix l a i)

/-- Full addressed result including preservation outside the written locations. -/
def image (l : Layout) (m : ℕ → ℕ) : Acc :=
  ([.clear,.cable,.delivery,.cableBins,.dataBins] : List Phase).foldl
    (fun a p => p.prefix l a (p.count l)) ⟨m,0,0⟩

/-- Registers 0–17 hold the constants, addresses and dimensions during all passes. -/
def Layout.param (l : Layout) : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 7
  | 6 => l.cables | 7 => l.cableCount | 8 => l.deliveries | 9 => l.deliveryCount
  | 10 => l.cells | 11 => l.heads | 12 => l.nodes | 13 => l.data
  | 14 => l.cableMean | 15 => l.dataMean | 16 => l.labels | 17 => l.labels*l.labels | _ => 0

/-- The physical registers and memory agree with the sparse directory and its totals. -/
def Ready (l : Layout) (a : Acc) (z : NatState) : Prop :=
  (∀ j : Reg, j.val < 18 → z.reg j = l.param j.val) ∧
    z.reg 18 = a.cableTotal ∧ z.reg 19 = a.dataTotal ∧ z.mem = a.mem

/-- Load the actual public frame and initialize both volumes. -/
def setup : Code := .block [
  .constant 0 0,.constant 1 1,.constant 2 2,.constant 3 3,.constant 4 4,.constant 5 7,
  readFrame 6 62 63 6,readFrame 7 62 63 7,readFrame 8 62 63 8,readFrame 9 62 63 9,
  readFrame 10 62 63 11,readFrame 11 62 63 49,readFrame 12 62 63 50,readFrame 13 62 63 51,
  readFrame 14 62 63 52,readFrame 15 62 63 53,readFrame 16 62 63 56,.binary .mul 17 16 16,
  .copy 18 0,.copy 19 0]

/-- Prepend the node with ordinal in register 25 to the incidence list of `cell`. -/
def insertNode (cell other dir : Reg) : Code := .block [
  .binary .add 26 11 cell,.load 27 26,.binary .mul 28 25 4,.binary .add 28 12 28,
  .store 28 27,.binary .add 28 28 1,.store 28 dir,.binary .add 28 28 1,.store 28 other,
  .binary .add 28 28 1,.store 28 24,.binary .add 29 25 1,.store 26 29]

/-- Native calculation for one compressed descriptor or initial bin. -/
def Phase.row : Phase → Code
  | .clear => .block [.binary .add 21 11 20,.store 21 0,.binary .add 21 13 20,.store 21 0]
  | .cable => .block [
    .binary .mul 21 20 3,.binary .add 21 6 21,.load 22 21,.binary .add 21 21 1,
    .load 23 21,.binary .add 21 21 1,.load 24 21,.ifEq 22 23 .nop (.block [.binary .mul 25 20 2,
      insertNode 22 23 0,.binary .add 25 25 1,insertNode 23 22 1,.binary .add 18 18 24])]
  | .delivery => .block [
    .binary .mul 21 20 5,.binary .add 21 8 21,.binary .add 21 21 4,.load 22 21,
    .binary .add 21 21 2,.load 24 21,.binary .add 26 13 22,.load 27 26,
    .binary .add 27 27 24,.store 26 27,.binary .add 19 19 24]
  | .cableBins => .block [.binary .add 21 14 20,.store 21 18]
  | .dataBins => .block [.binary .add 21 15 20,.binary .mul 24 19 16,.store 21 24]

/-- Register that holds a pass's length. -/
def Phase.boundReg : Phase → Reg
  | .clear => 10 | .cable => 7 | .delivery => 9 | .cableBins => 17 | .dataBins => 16

/-- One pass is a zero-initialized counted loop with a single cursor advance per row. -/
def Phase.scan (p : Phase) : Code := .seq (.constant 20 0)
  (.whileLt 20 p.boundReg (.seq p.row (.binary .add 20 20 1)))

/-- Fixed program that initializes the adjacency, per-cell loads and means. -/
def program : Code := .block [setup,Phase.clear.scan,Phase.cable.scan,Phase.delivery.scan,
  Phase.cableBins.scan,Phase.dataBins.scan]

/-- Initialization never branches nondeterministically or calls a private macro. -/
theorem program_deterministic : program.deterministic = true := by decide

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
