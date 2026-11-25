import OAI.Computability.VPVNP.SlotPacking

namespace OAI
/-! # Branch-independent field lengths in the native refresh stage directory -/

namespace ThreeFlat.Diagonal.RefreshStageLayout

open Computability.VPVNP.Compression
open scoped BigOperators

/-- All entries are counts of words. Base count, temporary port radix and
remaining lane count are the dynamic parameters; the expander degree and
padding are fixed for this template. -/
structure Counts where
  motifs : ℕ
  nodes : ℕ
  oldGraphRows : ℕ
  newGraphRows : ℕ
  oldWidthSpan : ℕ
  newWidthSpan : ℕ
  splitSpan : ℕ
  choiceSpan : ℕ
  graphSpan : ℕ
  sparseSpan : ℕ
  deriving DecidableEq

def counts (v m lanes h pad : ℕ) : Counts :=
  let d := 1+h+pad
  let M := v*lanes
  let oldRows := v*m
  let nextRows := oldRows*d
  ⟨M,oldRows*lanes,oldRows,nextRows,oldRows*(m*lanes),nextRows*lanes,
    3*oldRows,3*M,6*nextRows,M*m*h⟩

structure Pointers where
  dense : ℕ
  choice : ℕ
  sparse : ℕ
  next : ℕ
  firstNode : ℕ
  oldWidth : ℕ
  oldGraph : ℕ
  splitShift : ℕ
  newGraph : ℕ
  newWidth : ℕ
  deriving DecidableEq

/-- Actual relative field order consumed by the native pre- and post-admission
programs. The pointer allocator supplies absolute addresses; every count here
is independent of demands and of the guessed histogram. -/
def words (v m lanes h pad : ℕ) (p : Pointers) : ℕ → ℕ
  | 0 => (counts v m lanes h pad).motifs
  | 1 => p.dense
  | 2 => p.choice
  | 3 => p.sparse
  | 4 => p.next
  | 5 => (counts v m lanes h pad).nodes
  | 6 => p.firstNode
  | 7 => 0
  | 8 => lanes
  | 9 => p.oldWidth
  | 10 => p.oldGraph
  | 11 => (counts v m lanes h pad).oldGraphRows
  | 12 => p.splitShift
  | 13 => (counts v m lanes h pad).splitSpan
  | 14 => p.newGraph
  | 15 => (counts v m lanes h pad).newGraphRows
  | 16 => (counts v m lanes h pad).graphSpan
  | 17 => (counts v m lanes h pad).newWidthSpan
  | 18 => (counts v m lanes h pad).choiceSpan
  | 19 => p.newWidth
  | 20 => (counts v m lanes h pad).sparseSpan
  | _ => 0

/-- Additional persistent storage for one kernel and one local motif per
successor site, followed by the two incident-width records for each slot. -/
def headerExtra (C : Counts) (degree base : ℕ) : ℕ → ℕ
  | 34 => base
  | 35 => 5*C.nodes
  | 36 => base+5*C.nodes
  | 37 => 6*C.nodes
  | 38 => base+5*C.nodes+6*C.nodes
  | 39 => 2*C.nodes
  | 40 => base+5*C.nodes+6*C.nodes+2*C.nodes
  | 41 => 8*degree*C.nodes
  | 42 => base+(13+8*degree)*C.nodes
  | 43 => C.nodes
  | 44 => base+(14+8*degree)*C.nodes
  | 45 => C.nodes
  | _ => 0

def extraEnd (C : Counts) (degree base : ℕ) := headerExtra C degree base 44+headerExtra C degree base 45

theorem extra_extent (C : Counts) (degree base : ℕ) :
    extraEnd C degree base = base+(15+8*degree)*C.nodes := by
  change base+(14+8*degree)*C.nodes+C.nodes=base+(15+8*degree)*C.nodes
  rw [show 15+8*degree=(14+8*degree)+1 by omega,Nat.add_mul (14+8*degree) 1 C.nodes,one_mul,Nat.add_assoc]

variable {v a t h pad : ℕ}

/-- Independent check against the exact finite types traversed by the physical
kernel, old-site ordinal and three output scans. -/
theorem cardinalities :
    let C := counts v (2^a) (2^t) h pad
    C.motifs=Fintype.card (Fin v × BitWord t) ∧
    C.nodes=Fintype.card (Fin v × BitWord a × BitWord t) ∧
    C.oldGraphRows=Fintype.card (Fin v × Fin (2^a)) ∧
    C.newGraphRows=Fintype.card ((Fin v × Fin (2^a)) × Fin (1+h+pad)) ∧
    C.oldWidthSpan=Fintype.card ((Fin v × Fin (2^a)) × (BitWord a × BitWord t)) ∧
    C.newWidthSpan=Fintype.card (((Fin v × Fin (2^a)) × Fin (1+h+pad)) × BitWord t) ∧
    C.sparseSpan=Fintype.card (((Fin v × BitWord t) × Fin (2^a)) × Fin h) := by
  simp [counts,BitWord,Fintype.card_fin,ZMod.card,Nat.mul_assoc]

/-- A single current-site bound controls all dynamically allocated arrays;
the multiplier depends only on fixed port and expander degrees. -/
theorem bounded {v m lanes h pad K P : ℕ} (hm : 0 < m) (hl : 0<lanes) (hn : v*m*lanes≤P) :
    let C := counts v m lanes h pad
    C.motifs≤P ∧ C.nodes≤P ∧ C.oldGraphRows≤P ∧ C.newGraphRows≤(1+h+pad)*P ∧
    C.oldWidthSpan≤m*P ∧ C.newWidthSpan≤(1+h+pad)*P ∧ C.splitSpan≤3*P ∧
    C.choiceSpan≤3*P ∧ C.graphSpan≤6*(1+h+pad)*P ∧ C.sparseSpan≤h*P ∧ K*C.motifs≤K*P := by
  dsimp [counts]
  have hm' : v*lanes≤P := (Nat.mul_le_mul_right lanes (Nat.le_mul_of_pos_right v hm)).trans hn
  have hrow : v*m≤P := (Nat.le_mul_of_pos_right (v*m) hl).trans hn
  refine ⟨hm',hn,hrow,?_,?_,?_,Nat.mul_le_mul_left 3 hrow,Nat.mul_le_mul_left 3 hm',?_,?_,
    Nat.mul_le_mul_left K hm'⟩
  · simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (1+h+pad) hrow
  · simpa only [Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using Nat.mul_le_mul_left m hn
  · simpa only [Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using Nat.mul_le_mul_left (1+h+pad) hn
  · simpa only [Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using Nat.mul_le_mul_left (6*(1+h+pad)) hrow
  · simpa only [Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using Nat.mul_le_mul_left h hn

end ThreeFlat.Diagonal.RefreshStageLayout

end OAI
