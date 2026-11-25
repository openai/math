import OAI.Computability.BorderVNP.CubeISAHeaderInstallBoot
import OAI.Computability.BorderVNP.CubeLabelScratch
import OAI.Computability.BorderVNP.TransmissionTableAllocation
import OAI.Computability.BorderVNP.RoutingISACubeConstantArena

/-! # One length-only address allocation for the public and routed cube computation

The secondary header starts at the end of the emitted geometry. The packet and
singleton bits and the directory of owned vertex triples precede all public
tables and ordered pair views. The sparse receiving cell banks follow the
transmission directory and the pair views. Reservation of an unused word
incurs no time cost in the sparse RAM model.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally

/-- Length-only cube, geometric directory, and physical receiving-bank dimensions. -/
structure Layout where
  /-- Secondary header placed by the geometry allocator. -/
  header : CubeHeaderInstall.Inputs
  /-- One fewer than the fixed cube dimension. -/
  n : ℕ
  /-- Physical base demand width. -/
  b : ℕ
  /-- Number of edge slots in the fixed identity. -/
  h : ℕ
  /-- Fixed library of cube selectors. -/
  K : ℕ
  /-- Fixed relative supply width. -/
  s : ℕ
  /-- Number of allocated packed cell rows. -/
  cells : ℕ
  /-- Number of geometric cable slots, including empty rows. -/
  cables : ℕ
  /-- Capacity for emitted data and shared-range descriptors. -/
  maxRows : ℕ
  /-- Number of actual communicating teams. -/
  teams : ℕ
  /-- Spacing between the physical cell-input banks. -/
  cellStride : ℕ

/-- Product alphabet cardinality. -/
def Layout.alphabet (l : Layout) := l.header.d^(l.n+1)

/-- The high-water word of the native packet bank, including unused trials. -/
def Layout.packetEnd (l : Layout) :=
  CubeHeaderInstall.bankStop l.header l.n (bankWidth l.n l.b l.h l.K l.s)

/-- Raw singleton bits begin after the row checker’s descriptor and its edge-digit workspace. -/
def Layout.singleBank (l : Layout) := l.packetEnd+8+l.h

/-- Address of the directory of local packet vertices. -/
def Layout.vertexBase (l : Layout) :=
  l.singleBank+l.alphabet^2*(l.header.blocks*(l.h*l.b))

/-- The directory reserves every packet candidate at each outer role and
every binary corner. The accepted traversal writes only owned, valid triples. -/
def Layout.vertexCap (l : Layout) :=
  l.header.d^2*Physical.Owned.packetTrials l.n l.header.d l.header.blocks*2^(l.n+1)

/-- Base of the native label chooser's six arrays, after the vertex triples. -/
def Layout.publicBase (l : Layout) := l.vertexBase+3*l.vertexCap

/-- Head pointers in the public sparse cable incidence lists. -/
def Layout.heads (l : Layout) := l.publicBase+l.cells

/-- Two four-word adjacency nodes per cable slot. -/
def Layout.nodes (l : Layout) := l.heads+l.cells

/-- Delivery totals at each actual receiving cell. -/
def Layout.demands (l : Layout) := l.nodes+8*l.cables

/-- Ordered-pair mean accumulators used in the label chooser. -/
def Layout.cableMean (l : Layout) := l.demands+l.cells

/-- One mean for incoming literal width per label. -/
def Layout.dataMean (l : Layout) := l.cableMean+l.alphabet^2

/-- Directed label-pair widths computed from the chosen labels and physical cables. -/
def Layout.widthBase (l : Layout) := l.dataMean+l.alphabet

/-- One ordinal within a directed pair per geometric cable. -/
def Layout.ordinalBase (l : Layout) := l.widthBase+l.alphabet^2

/-- Little-endian digit place values for each axis. -/
def Layout.powerBase (l : Layout) := l.ordinalBase+l.cables

/-- Team-load histogram starts after the powers. -/
def Layout.groupWeights (l : Layout) := l.powerBase+(l.n+1)

/-- Accumulated group weights for each team. -/
def Layout.teamTotals (l : Layout) := l.groupWeights+l.header.d

/-- Greedy owner numbers for each grouping symbol. -/
def Layout.ownerBase (l : Layout) := l.teamTotals+l.teams

/-- Classification and packet family index of every ordered pair of product labels. -/
def Layout.pairDirectory (l : Layout) := l.ownerBase+l.header.d

/-- Two-word rows giving each cell's assigned team and absolute physical bank. -/
def Layout.hostDirectory (l : Layout) := l.pairDirectory+3*l.alphabet^2

/-- Seven-word transmission rows begin after the physical receiving-cell directory. -/
def Layout.records (l : Layout) := l.hostDirectory+2*l.cells

/-- View of the actual routing table at a particular realized row count. -/
def Layout.table (l : Layout) (frame count : ℕ) :=
  TableLayout.reserve frame l.records l.teams l.maxRows count

/-- Pair views start after all four compiled routing-address arrays. -/
def Layout.pairBase (l : Layout) := TableLayout.reserveEnd l.records l.teams l.maxRows

/-- Each oriented group-pair view has room for its entire transmitted selector
prefix and the largest legal declared crossing suffix. -/
def Layout.pairStride (l : Layout) :=
  l.header.volume l.n (selectorWidth l.n l.K l.h)+l.header.cap+1

/-- First opaque receiving-cell bank. -/
def Layout.cellBank (l : Layout) := l.pairBase+l.header.d^2*l.pairStride

/-- First free address available for the static cube tables or subsequent tasks. -/
def Layout.stop (l : Layout) := l.cellBank+l.cells*l.cellStride

/-- The bounds between the actual computation, singleton bits, vertex triples,
public tables, and ordered streams hold for all dimensions and lengths. -/
theorem Layout.separated (l : Layout) :
    l.packetEnd+8+l.h = l.singleBank ∧ l.singleBank ≤ l.vertexBase ∧
    l.vertexBase+3*l.vertexCap = l.publicBase ∧ l.publicBase ≤ l.pairBase ∧
    l.pairBase+l.header.d^2*l.pairStride = l.cellBank ∧ l.cellBank ≤ l.stop := by
  refine ⟨rfl,Nat.le_add_right ..,rfl,?_,rfl,Nat.le_add_right ..⟩
  simp only [pairBase,TableLayout.reserveEnd,records,hostDirectory,pairDirectory,ownerBase,teamTotals,
    groupWeights,powerBase,ordinalBase,widthBase,dataMean,cableMean,demands,nodes,heads,Nat.add_assoc]
  exact Nat.le_add_right ..

/-- The true routing allocation uses exactly the announced pointers and lies
completely below every ordered pair view. -/
theorem Layout.table_allocated (l : Layout) {w frame count : ℕ} (R : 2 < l.teams)
    (low : frame+31 ≤ l.records) (rows : count ≤ l.maxRows) (high : l.stop < 2^w) :
    (l.table frame count).Allocated w ∧
      (l.table frame count).ordinals+(l.table frame count).count ≤ l.pairBase := by
  have near : l.pairBase ≤ l.stop := by unfold stop cellBank; omega
  exact ⟨TableLayout.reserve_allocated R low rows (near.trans_lt high),TableLayout.reserve_extent rows⟩

/-- Upper bound for every bit in a valid ordered pair view, including a
selector-length prefix and a declared crossing count. -/
theorem Layout.view_lt_cellBank (l : Layout) (x y : Fin l.header.d) {j : ℕ}
    (hj : j < l.pairStride) :
    l.pairBase+l.pairStride*(x.val*l.header.d+y.val)+j < l.cellBank := by
  have ix := x.isLt
  have iy := y.isLt
  have row : x.val*l.header.d+y.val < l.header.d^2 := by
    calc
      _ < (x.val+1)*l.header.d := by rw [Nat.add_mul]; omega
      _ ≤ _ := by rw [pow_two]; exact Nat.mul_le_mul_right _ ix
  have step := Nat.mul_le_mul_left l.pairStride row
  unfold cellBank
  rw [Nat.mul_comm (l.header.d^2) l.pairStride]
  rw [Nat.mul_succ] at step
  omega

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
