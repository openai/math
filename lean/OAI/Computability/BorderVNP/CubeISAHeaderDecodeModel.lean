import OAI.Computability.BorderVNP.CubeISAHeaderOffsets
import OAI.Computability.BorderVNP.CubeISASelectorRead

/-! # Reading the compact cube declaration into its public word arrays

The source begins after the branch bit and epoch profile. Its first field
is the grouping coordinate. Only upper-triangular symbol pairs occupy input
bits. The RAM output has a zero-filled lower triangle.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.HeaderDecode

open VPVNP.BurstRAM Cube.DeclarationBits Cube.SelectorRead

/-- Fixed scalar and array layout, before looking at any candidate bits. -/
structure Layout where
  /-- Address of the secondary declaration header. -/
  header : ℕ
  /-- First source bit address, after the branch and epoch profile. -/
  source : ℕ
  /-- Alphabet size. -/
  d : ℕ
  /-- Number of candidate directions. -/
  a : ℕ
  /-- Width of the grouping coordinate word. -/
  cw : ℕ
  /-- Width of one declared row entry. -/
  rw : ℕ
  /-- Largest legal row entry. -/
  cap : ℕ
  /-- Base of the dense claimed rows. -/
  dense : ℕ
  /-- Base of the public directional totals. -/
  totals : ℕ

/-- Number of physical dense entries, including the zero lower triangle. -/
def Layout.entries (l : Layout) := l.d*l.d*l.a

/-- Address of the next upper-triangular input field at a dense cursor. -/
def Layout.start (l : Layout) := fieldStart l.source l.d l.a l.cw l.rw

/-- The declared coordinate followed by every transmitted row word passes its
individual binary and range tests. -/
def Valid (l : Layout) (m : ℕ → ℕ) : Prop :=
  Cube.SelectorRead.Valid m l.source l.cw l.a ∧
    ∀ k < l.entries, upper l.d l.a k → Cube.SelectorRead.Valid m (l.start k) l.rw (l.cap+1)

/-- Value to store for one dense row entry. -/
def Layout.value (l : Layout) (m : ℕ → ℕ) (k : ℕ) :=
  if upper l.d l.a k then (decoded m (l.start k) l.rw).val else 0

/-- Complete memory image after the coordinate and a prefix of the dense array. -/
def Layout.image (l : Layout) (m : ℕ → ℕ) (k addr : ℕ) :=
  if l.dense ≤ addr ∧ addr < l.dense+k then l.value m (addr-l.dense)
  else if addr = l.header+5 then (decoded m l.source l.cw).val else m addr

/-- The input and all outputs have representable addresses and are disjoint. -/
structure Fits (l : Layout) (w : ℕ) : Prop where
  /-- Literals zero, one and two are available. -/
  small : 2 < 2^w
  /-- The exclusive range bound for row values is representable. -/
  bound : l.cap+1 < 2^w
  /-- Coordinate field fits the decoder's word. -/
  coordWidth : l.cw ≤ w
  /-- Row field fits the decoder's word. -/
  rowWidth : l.rw ≤ w
  /-- Positive cut dimension. -/
  dimension : 0 < l.a
  /-- Exclusive array count fits a counter. -/
  count : l.entries < 2^w
  /-- Last output address for the dense table fits. -/
  denseEnd : l.dense+l.entries ≤ 2^w
  /-- Coordinate cell is addressable. -/
  coordinate : l.header+5 < 2^w
  /-- All cursor positions up to the end are representable. -/
  stream : l.start l.entries < 2^w
  /-- No dense write aliases the coordinate cell. -/
  different : l.header+5 < l.dense ∨ l.dense+l.entries ≤ l.header+5
  /-- The compact input is disjoint from the dense output. -/
  sourceRows : l.start l.entries ≤ l.dense ∨ l.dense+l.entries ≤ l.source
  /-- The compact input is disjoint from the coordinate output. -/
  sourceCoordinate : l.header+5 < l.source ∨ l.start l.entries ≤ l.header+5

/-- Natural input address after the next candidate position. -/
theorem Layout.start_succ (l : Layout) (k : ℕ) :
    l.start (k+1) = l.start k + if upper l.d l.a k then l.rw else 0 := by
  by_cases h : upper l.d l.a k <;> simp [Layout.start,fieldStart,fieldsBefore,h,Nat.add_mul,Nat.add_assoc]

/-- The compact cursor never retreats. -/
theorem Layout.start_mono (l : Layout) : Monotone l.start :=
  monotone_nat_of_le_succ fun k => by rw [l.start_succ]; omega

/-- One dense store extends the exact memory image by a single word. -/
theorem Layout.image_step (l : Layout) (m : ℕ → ℕ) (k : ℕ) :
    Function.update (l.image m k) (l.dense+k) (l.value m k) = l.image m (k+1) := by
  funext addr
  by_cases h : addr = l.dense+k
  · subst addr
    simp [Layout.image]
  · rw [Function.update_of_ne h]
    have eq : l.dense ≤ addr ∧ addr < l.dense+k+1 ↔ l.dense ≤ addr ∧ addr < l.dense+k := by omega
    simp only [Layout.image,← Nat.add_assoc,eq]

/-- Every read in the compact input sees the original word throughout the traversal. -/
theorem Fits.input {l : Layout} {w k addr : ℕ} (room : Fits l w) (m : ℕ → ℕ) (hk : k ≤ l.entries)
    (lo : l.source ≤ addr) (hi : addr < l.start l.entries) : l.image m k addr = m addr := by
  have r := room.sourceRows
  have c := room.sourceCoordinate
  simp [Layout.image,show ¬(l.dense ≤ addr ∧ addr < l.dense+k) by omega,show addr ≠ l.header+5 by omega]

/-- Reader validity and decoded ordinal depend only on the visited compact bits. -/
theorem decoded_congr (m m' : ℕ → ℕ) (base bits count : ℕ) (h : ∀ j < bits, m (base+j) = m' (base+j)) :
    decoded m base bits = decoded m' base bits ∧
    (Cube.SelectorRead.Valid m base bits count ↔ Cube.SelectorRead.Valid m' base bits count) := by
  have he : decoded m base bits = decoded m' base bits := by
    apply congrArg (VPVNP.RAMSerialization.wordBits _).symm
    exact funext fun j => by rw [h j.val j.isLt]
  exact ⟨he,by unfold Cube.SelectorRead.Valid; rw [he]; exact and_congr_left' (forall_congr' fun j =>
    forall_congr' fun hj => by rw [h j hj])⟩

/-- Read primary and secondary metadata; registers 30--34 are also the input
registers for the subsequent column-total computation. -/
def setup : Code := .block [
  readFrame 28 62 63 59, CubeLengths.field 29 2, CubeLengths.field 30 1, CubeLengths.field 31 3,
  CubeLengths.field 32 4, .binary .mul 33 28 28, CubeLengths.field 34 12,
  CubeLengths.field 20 10,CubeLengths.field 21 11,readFrame 22 62 63 63,.constant 62 5,
  .binary .add 22 22 62,readFrame 24 62 63 25,.constant 25 1,.binary .add 24 24 25,
  CubeLengths.field 62 9,.binary .add 24 24 62,.constant 23 0,.copy 41 20,.copy 42 32]

/-- Store the chosen coordinate, advance over its encoded bits, and install the
decoder's width and exclusive bound for the row fields. -/
def beginRows : Code := .block [.store 22 43,.binary .add 24 24 20,.copy 41 21,.binary .add 42 34 25]

/-- Decode the row and column symbol indices from the dense ordinal. -/
def classify : Code := .block [.binary .div 35 23 32,.binary .div 36 35 28,.binary .mod 37 35 28]

/-- A real upper field consumes exactly one width; a lower field only supplies zero. -/
def fieldValue : Code := .ifLt 37 36 (.constant 43 0) (.seq reader (.binary .add 24 24 21))

/-- Store the decoded value or padding zero and advance the dense ordinal. -/
def writeValue : Code := .block [.binary .add 27 30 23,.store 27 43,.binary .add 23 23 25]

/-- One dense table iteration. -/
def step : Code := .seq classify (.seq fieldValue writeValue)

/-- Full fixed instruction sequence for the compact header. -/
def decode : Code := .seq setup (.seq reader (.seq beginRows (.whileLt 23 29 step)))

/-- The public registers retained for column aggregation after the header scan. -/
structure Static (l : Layout) (reg : Reg → ℕ) : Prop where
  /-- Coordinate bit width. -/
  cw : reg 20 = l.cw
  /-- Entry bit width. -/
  rw : reg 21 = l.rw
  /-- Chosen coordinate cell in the secondary header. -/
  chosen : reg 22 = l.header+5
  /-- Unit increment. -/
  one : reg 25 = 1
  /-- Symbol alphabet size. -/
  d : reg 28 = l.d
  /-- Dense loop bound. -/
  count : reg 29 = l.entries
  /-- Row array base. -/
  dense : reg 30 = l.dense
  /-- Total array base. -/
  totals : reg 31 = l.totals
  /-- Direction count. -/
  a : reg 32 = l.a
  /-- Square symbol-row count. -/
  rows : reg 33 = l.d*l.d
  /-- Largest legal entry. -/
  cap : reg 34 = l.cap

/-- The exact registers and prefix memory reached by the traversal. -/
structure State (l : Layout) (old : ℕ → ℕ) (k : ℕ) (z : NatState) : Prop where
  /-- Fixed loop data. -/
  fixed : Static l z.reg
  /-- Current dense entry. -/
  cursor : z.reg 23 = k
  /-- Actual compact-stream pointer. -/
  compact : z.reg 24 = l.start k
  /-- Width of the active row word. -/
  bits : z.reg 41 = l.rw
  /-- Exclusive bound on the active word. -/
  bound : z.reg 42 = l.cap+1
  /-- Image after the first dense entries. -/
  memory : z.mem = l.image old k

end RoutingISA.HeaderDecode

end BorderVNP
end Computability
end OAI
