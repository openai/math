import OAI.Computability.BorderVNP.RoutingISATableState
import OAI.Computability.BorderVNP.RoutingISAAddressProof

/-! # Allocated arrays and their mathematical scheduling image

The input frame names all six disjoint address intervals. Transmission records use seven
words. The scheduler reads their kind, endpoints, and width. The remaining fields describe
payload locations and are left untouched. The output width table is upper triangular and
the ordinal of a record is the prefix width of its endpoint pair.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open Finset

/-- Memory intervals occupied by the scheduler. -/
inductive TableArray where
  | frame | records | widths | offsets | used | ordinals
  deriving DecidableEq

/-- Addresses and dimensions carried by the packed scheduling frame. -/
structure TableLayout where
  /-- Base of the public frame. -/
  frame : ℕ
  /-- Number of physical teams. -/
  teams : ℕ
  /-- Number of transmission records. -/
  count : ℕ
  /-- Base of the array of seven-word transmission records. -/
  records : ℕ
  /-- Base of the square table of pair widths. -/
  widths : ℕ
  /-- Base of the cubic table of partner offsets. -/
  offsets : ℕ
  /-- Base of the square table of oriented leg totals. -/
  used : ℕ
  /-- Base of the transmission record prefix ordinals. -/
  ordinals : ℕ

/-- Initial address of an allocated interval. -/
def TableLayout.base (l : TableLayout) : TableArray → ℕ
  | .frame => l.frame
  | .records => l.records
  | .widths => l.widths
  | .offsets => l.offsets
  | .used => l.used
  | .ordinals => l.ordinals

/-- Number of words occupied by the corresponding interval. -/
def TableLayout.length (l : TableLayout) : TableArray → ℕ
  | .frame => 21
  | .records => 7*l.count
  | .widths | .used => l.teams^2
  | .offsets => l.teams^3
  | .ordinals => l.count

/-- Membership in the allocated half-open interval, using ordinary word addresses. -/
def TableLayout.contains (l : TableLayout) (a : TableArray) (i : ℕ) : Prop :=
  l.base a ≤ i ∧ i < l.base a+l.length a

/-- The six intervals are disjoint and addressable, including the square loop bound
stored as a word and the positive relay period `teams-2`. -/
structure TableLayout.Allocated (l : TableLayout) (w : ℕ) : Prop where
  /-- At least three teams are available. -/
  teamCount : 2 < l.teams
  /-- The squared team count itself fits a register. -/
  square : l.teams^2 < 2^w
  /-- Every occupied address fits an unsigned word. -/
  fits : ∀ a, l.base a + l.length a ≤ 2^w
  /-- Distinct arrays occupy disjoint intervals. -/
  separate : ∀ a b i, a ≠ b → l.contains a i → ¬ l.contains b i

/-- Public transmission columns accessed during schedule construction. -/
structure TableRow where
  /-- Kind zero or one. -/
  kind : ℕ
  /-- First team endpoint. -/
  first : ℕ
  /-- Second team endpoint. -/
  second : ℕ
  /-- The number of wire bits carried by this record. -/
  width : ℕ

/-- Register values shared by the setup and the scheduling loops. -/
def TableLayout.regValue (l : TableLayout) : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => l.teams | 4 => l.teams*l.teams | 5 => l.teams-2
  | 6 => l.records | 7 => l.count | 8 => l.widths | 9 => l.offsets | 10 => l.used
  | 11 => l.ordinals | 12 => 7 | _ => 0

/-- The thirteen persistent configuration registers have their declared contents. -/
def TableLayout.ready (l : TableLayout) (s : NatState) : Prop :=
  ∀ j : Reg, j.val ≤ 12 → s.reg j = l.regValue j.val

/-- Straight-line code writing only scratch registers preserves the scheduling configuration. -/
theorem TableLayout.ready_fixed {l : TableLayout} {z : NatState} (h : l.ready z)
    {c : Code} (hc : c.protects 13 = true) (pub : Arg → ℕ) : l.ready (c.fixedEval pub z) := by
  intro j hj
  exact (c.fixedEval_protected pub z hc j (by omega)).trans (h j hj)

/-- The frame slot values loaded by the scheduler. -/
def TableLayout.frameFields (l : TableLayout) (mem : ℕ → ℕ) : Prop :=
  mem (l.frame+1) = l.teams ∧ mem (l.frame+12) = l.records ∧ mem (l.frame+13) = l.count ∧
  mem (l.frame+16) = l.widths ∧ mem (l.frame+17) = l.offsets ∧ mem (l.frame+18) = l.used ∧
  mem (l.frame+20) = l.ordinals

/-- Contents of the four columns of the transmission record used by the public pass. -/
def TableLayout.recordsMatch (l : TableLayout) (row : ℕ → TableRow) (mem : ℕ → ℕ) : Prop :=
  ∀ i < l.count, let b := 7*i+l.records
    mem b = (row i).kind ∧ mem (b+1) = (row i).first ∧
      mem (b+2) = (row i).second ∧ mem (b+3) = (row i).width

/-- Row-major unordered pair key, always in the upper triangle. -/
def TableLayout.pairKey (l : TableLayout) (u v : ℕ) : ℕ := min u v*l.teams+max u v

/-- Width contributed to a specific pair by a prefix of the descriptor table. -/
def TableLayout.pairWidth (l : TableLayout) (row : ℕ → TableRow) (i key : ℕ) : ℕ :=
  ∑ j ∈ range i, if (row j).first ≠ (row j).second ∧ l.pairKey (row j).first (row j).second = key
    then (row j).width else 0

/-- The starting ordinal assigned to a transmission interval by the public pass. -/
def TableLayout.ordinal (l : TableLayout) (row : ℕ → TableRow) (i : ℕ) : ℕ :=
  if (row i).first = (row i).second then 0 else l.pairWidth row i (l.pairKey (row i).first (row i).second)

/-- One partner's length on an oriented leg, from the actual round-robin schedule. -/
def TableLayout.partnerLength (l : TableLayout) (row : ℕ → TableRow) (u v j : ℕ) : ℕ :=
  if h : u < l.teams ∧ v < l.teams ∧ j < l.teams then
    Routing.scheduledLength ⟨u,h.1⟩ ⟨j,h.2.2⟩ ⟨v,h.2.1⟩ (l.pairWidth row l.count (l.pairKey u j))
  else 0

/-- Offset of partner `j`, or total length at the terminal index `j=teams`. -/
def TableLayout.legPrefix (l : TableLayout) (row : ℕ → TableRow) (u v j : ℕ) : ℕ :=
  ∑ k ∈ range j, l.partnerLength row u v k

/-- Well-formed public endpoint descriptors with addressable total widths. -/
structure TableLayout.RowsFit (l : TableLayout) (w : ℕ) (row : ℕ → TableRow) : Prop where
  /-- All records have a valid kind and two in-range endpoints. -/
  labels : ∀ i < l.count, (row i).kind < 2 ∧ (row i).first < l.teams ∧ (row i).second < l.teams
  /-- Sum of every recorded width fits in one word. -/
  widths : (∑ i ∈ range l.count, (row i).width) < 2^w

/-- A stored index has the form base plus an offset within the corresponding array. -/
theorem TableLayout.contains_offset (l : TableLayout) {a : TableArray} {i : ℕ} (hi : i < l.length a) :
    l.contains a (l.base a+i) := ⟨Nat.le_add_right .., Nat.add_lt_add_left hi _⟩

/-- Prefix pair width is at most the sum of the original widths, independent of the number
of represented bits. -/
theorem TableLayout.pairWidth_le_sum (l : TableLayout) (row : ℕ → TableRow) {i : ℕ}
    (hi : i ≤ l.count) (key : ℕ) : l.pairWidth row i key ≤ ∑ j ∈ range l.count, (row j).width :=
  (Finset.sum_le_sum fun j _ => by split <;> omega).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hi) fun _ _ _ => Nat.zero_le _)

end RoutingISA

end BorderVNP
end Computability
end OAI
