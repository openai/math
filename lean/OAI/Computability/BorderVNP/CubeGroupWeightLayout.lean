import OAI.Computability.BorderVNP.CubeTeamNativeBudget

/-! # Inputs and exact prefix weights of the group histogram -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open RoutingISA VPVNP.BurstRAM

/-- Public word addresses and dimensions for constructing the group-weight vector. -/
structure Layout where
  /-- Native frame base and declaration-header base. -/
  frame : ℕ
  /-- Base of the secondary declaration header. -/
  header : ℕ
  /-- Alphabet of symbols, number of cube axes and selected axis. -/
  groups : ℕ
  /-- Number of cube coordinates. -/
  axes : ℕ
  /-- Selected grouping coordinate. -/
  axis : ℕ
  /-- Crossing matrix base, fixed off-diagonal selector length and output weight array. -/
  rows : ℕ
  /-- Fixed number of selector bits in each strict symbol row. -/
  selectors : ℕ
  /-- Base of the output group-weight array. -/
  weights : ℕ
  /-- Count of packed cells, their labels and their incoming data totals. -/
  cells : ℕ
  /-- Base of the packed-cell product-label array. -/
  labels : ℕ
  /-- Base of the incoming bit widths per cell. -/
  demands : ℕ
  /-- Public table of alphabet powers and number of product labels. -/
  powers : ℕ
  /-- Number of product labels. -/
  alphabet : ℕ
  /-- Number of wires per packet block and number of blocks per ordered label pair. -/
  blockWidth : ℕ
  /-- Number of packet blocks per ordered pair of product labels. -/
  blocks : ℕ

/-- Place value of the grouping coordinate in the little-endian label code. -/
def Layout.place (l : Layout) := l.groups^l.axis

/-- Raw charge for one symbol, obtained by inclusion and exclusion of the two ends. -/
def Layout.raw (l : Layout) :=
  l.blocks*l.blockWidth*(l.alphabet/l.groups)*(2*l.alphabet-l.alphabet/l.groups)

/-- Row location of an unordered symbol pair in the declared square matrix. -/
def Layout.rowAddr (l : Layout) (s t : ℕ) :=
  l.rows + ((min s t)*l.groups + max s t)*l.axes + l.axis

/-- Numeric grouping symbol of a packed cell. -/
def Layout.symbol (l : Layout) (orig : ℕ → ℕ) (c : ℕ) :=
  orig (l.labels+c) / l.place % l.groups

/-- Contribution to group `s` from one ordered pair of symbols.
The two orders count incidence separately at the two ends. -/
def Layout.rowCharge (l : Layout) (orig : ℕ → ℕ) (q s : ℕ) :=
  if q/l.groups = s ∧ s ≠ q%l.groups then orig (l.rowAddr s (q%l.groups)) + l.selectors else 0

/-- Incoming bits at a cell are charged once to its receiving group. -/
def Layout.dataCharge (l : Layout) (orig : ℕ → ℕ) (c s : ℕ) :=
  if l.symbol orig c = s then orig (l.demands+c) else 0

/-- Shared width incident to a symbol after the first `k` ordered-pair reads. -/
def Layout.sharedTotal (l : Layout) (orig : ℕ → ℕ) (k s : ℕ) :=
  ∑ q ∈ Finset.range k, l.rowCharge orig q s

/-- Delivery width after the first `k` packed-cell reads. -/
def Layout.dataTotal (l : Layout) (orig : ℕ → ℕ) (k s : ℕ) :=
  ∑ c ∈ Finset.range k, l.dataCharge orig c s

/-- Exact value to store at group `s`. -/
def Layout.weight (l : Layout) (orig : ℕ → ℕ) (s : ℕ) :=
  TeamNative.scaledWeight (l.sharedTotal orig (l.groups*l.groups) s) (l.dataTotal orig l.cells s) l.raw

/-- Initialization, incident declaration reads and incoming data reads. -/
inductive Phase | init | shared | data
  deriving DecidableEq

/-- Each square-matrix read or packed-cell read occurs only once in its pass. -/
def Phase.count (p : Phase) (l : Layout) := match p with
  | .init => l.groups | .shared => l.groups*l.groups | .data => l.cells

/-- Exact weight after a prefix of a pass. -/
def Phase.value (p : Phase) (l : Layout) (orig : ℕ → ℕ) (i s : ℕ) := match p with
  | .init => if s < i then l.raw else orig (l.weights+s)
  | .shared => TeamNative.scaledWeight (l.sharedTotal orig i s) 0 l.raw
  | .data => TeamNative.scaledWeight (l.sharedTotal orig (l.groups*l.groups) s) (l.dataTotal orig i s) l.raw

/-- Exact prefix contents of every output word, with all other addresses preserved. -/
structure Image (p : Phase) (l : Layout) (orig mem : ℕ → ℕ) (i : ℕ) : Prop where
  /-- Output words, including unprocessed slots in the initialization pass. -/
  weights : ∀ s < l.groups, mem (l.weights+s) = p.value l orig i s
  /-- The program only writes the group-weight interval. -/
  outside : ∀ a, (∀ s < l.groups, a ≠ l.weights+s) → mem a = orig a

/-- Expected stable values loaded by the physical setup. -/
def Layout.param (l : Layout) : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 1000000 | 3 => l.groups | 4 => l.axes
  | 5 => l.axis | 6 => l.rows | 7 => l.selectors | 8 => l.weights
  | 9 => l.cells | 10 => l.labels | 11 => l.demands | 12 => l.place
  | 13 => l.raw | 14 => l.groups*l.groups | _ => 0

/-- Stable register prefix for the three scans. -/
def Layout.Ready (l : Layout) (z : NatState) := ∀ j : Reg, j.val < 15 → z.reg j = l.param j.val

/-- All addresses actually touched during the public scans fit their word and the
input cells stay disjoint from the output interval. -/
structure Layout.Fits (l : Layout) (w : ℕ) (orig : ℕ → ℕ) : Prop where
  positive : 0 < l.groups
  square : l.groups*l.groups < 2^w
  weights : ∀ s < l.groups, l.weights+s < 2^w
  rows : ∀ s < l.groups, ∀ t < l.groups, l.rowAddr s t < 2^w
  labels : ∀ c < l.cells, l.labels+c < 2^w
  demands : ∀ c < l.cells, l.demands+c < 2^w
  rowSep : ∀ s < l.groups, ∀ t < l.groups, ∀ u < l.groups, l.rowAddr s t ≠ l.weights+u
  labelSep : ∀ c < l.cells, ∀ u < l.groups, l.labels+c ≠ l.weights+u
  dataSep : ∀ c < l.cells, ∀ u < l.groups, l.demands+c ≠ l.weights+u
  /-- Only the final nonnegative weight needs a separate volume bound. -/
  weightsFit : ∀ s < l.groups, l.weight orig s < 2^w

/-- Prefixes of a nonnegative histogram are bounded by the final group word. -/
theorem value_le_weight {l : Layout} {orig : ℕ → ℕ} (p : Phase) (hp : p ≠ .init)
    (i s : ℕ) (hi : i ≤ p.count l) : p.value l orig i s ≤ l.weight orig s := by
  have hs {i j : ℕ} (h : i ≤ j) : l.sharedTotal orig i s ≤ l.sharedTotal orig j s :=
    Finset.sum_le_sum_of_subset (Finset.range_mono h)
  have hd {i j : ℕ} (h : i ≤ j) : l.dataTotal orig i s ≤ l.dataTotal orig j s :=
    Finset.sum_le_sum_of_subset (Finset.range_mono h)
  cases p with
  | init => contradiction
  | shared =>
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    exact Nat.add_le_add (hs hi) (Nat.zero_le _)
  | data =>
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    exact Nat.add_le_add_left (hd hi) _

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
